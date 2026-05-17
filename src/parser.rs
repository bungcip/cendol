//! Parser module for C11 compiler
//!
//! This module provides the main parser coordination, public API, and state management.
//! It orchestrates the parsing process by delegating to specialized sub-modules for
//! different language constructs.

use crate::ast::literal::{LitKind, LitRef};
use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::CStandard;

use crate::source_manager::SourceSpan;

pub mod declarations;
pub mod declarator;
pub mod enum_parsing;
pub mod errors;
pub mod expressions;
pub mod lexer;
pub mod statements;
pub mod struct_parsing;
pub mod type_builder;
pub mod type_specifiers;
pub mod utils;

// Re-export commonly used types
pub(crate) use crate::parser::errors::{ParseDiag, ParseError};
pub(crate) use expressions::BindingPower;
use expressions::parse_expression;
pub(crate) use lexer::{Lexer, Token, TokenKind};

/// Type context for tracking typedef names and other type-related state
/// Bolt ⚡: Optimized with a HashMap and shadow stacks for O(1) lookup.
/// Shadowing is handled by storing a stack of (bool) for each identifier.
#[derive(Debug)]
pub(crate) struct TypeDefContext {
    /// Stack of scopes, each containing a list of names modified in that scope.
    /// This is used to unwind the `map` when popping or truncating scopes.
    scopes: Vec<Vec<NameId>>,
    /// Fast lookup table: NameId -> Stack of (is_typedef) values.
    /// SmallVec[1] ensures that common, non-shadowed names don't allocate on the heap.
    map: hashbrown::HashMap<NameId, smallvec::SmallVec<[bool; 1]>>,
}

impl TypeDefContext {
    /// Create a new type context with builtin typedefs
    fn new() -> Self {
        let mut ctx = TypeDefContext {
            scopes: vec![Vec::new()],
            map: hashbrown::HashMap::new(),
        };

        let globals = [
            "int8_t", "int16_t", "int32_t", "int64_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t",
        ];

        for name in globals {
            ctx.add_typedef(NameId::new(name));
        }

        ctx
    }

    /// Check if a symbol is a typedef name
    #[inline]
    fn is_type_name(&self, symbol: NameId) -> bool {
        self.map.get(&symbol).is_some_and(|stack| *stack.last().unwrap())
    }

    /// Add a typedef name
    fn add_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push(symbol);
        self.map.entry(symbol).or_default().push(true);
    }

    /// Add a non-typedef name (e.g. variable or function) that shadows outer typedefs
    fn add_non_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push(symbol);
        self.map.entry(symbol).or_default().push(false);
    }

    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    fn pop_scope(&mut self) {
        let names = self.scopes.pop().expect("pop_scope on empty TypeDefContext");
        for name in names {
            let stack = self.map.get_mut(&name).unwrap();
            stack.pop();
            if stack.is_empty() {
                self.map.remove(&name);
            }
        }
    }

    fn get_last_scope_len(&self) -> usize {
        self.scopes.last().map(|s| s.len()).unwrap_or(0)
    }

    fn truncate_last_scope(&mut self, len: usize) {
        if let Some(scope) = self.scopes.last_mut() {
            while scope.len() > len {
                let name = scope.pop().unwrap();
                let stack = self.map.get_mut(&name).unwrap();
                stack.pop();
                if stack.is_empty() {
                    self.map.remove(&name);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ParserState {
    current_idx: usize,
    diag_len: usize,
    type_context_last_scope_len: usize,
}

/// Main parser structure
pub struct Parser<'arena, 'src, 'lexer> {
    pub(crate) lexer: &'lexer mut Lexer<'src>,
    pub(crate) current_idx: usize,
    pub(crate) ast: &'arena mut ParsedAst,
    pub(crate) lang_opts: &'src crate::lang_options::LangOptions,

    // Token caching for lookahead and backtracking
    pub(crate) token_cache: Vec<Token>,

    // Type context for typedef tracking
    pub(crate) type_context: TypeDefContext,
    pub(crate) keywords: ParserKeywords,

    /// Flag to indicate if we are parsing an enum's underlying type
    pub(crate) in_enum_underlying_type: bool,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ParserKeywords {
    pub(crate) attr_noreturn: NameId,
    pub(crate) attr_noreturn_underscore: NameId,
    pub(crate) attr_aligned: NameId,
    pub(crate) attr_aligned_underscore: NameId,
    pub(crate) attr_packed: NameId,
    pub(crate) attr_packed_underscore: NameId,
    pub(crate) attr_cleanup: NameId,
    pub(crate) attr_cleanup_underscore: NameId,
}

impl ParserKeywords {
    fn new() -> Self {
        ParserKeywords {
            attr_noreturn: NameId::new("noreturn"),
            attr_noreturn_underscore: NameId::new("__noreturn__"),
            attr_aligned: NameId::new("aligned"),
            attr_aligned_underscore: NameId::new("__aligned__"),
            attr_packed: NameId::new("packed"),
            attr_packed_underscore: NameId::new("__packed__"),
            attr_cleanup: NameId::new("cleanup"),
            attr_cleanup_underscore: NameId::new("__cleanup__"),
        }
    }
}

impl<'arena, 'src, 'lexer> Parser<'arena, 'src, 'lexer> {
    /// Create a new parser
    pub(crate) fn new(
        lexer: &'lexer mut Lexer<'src>,
        ast: &'arena mut ParsedAst,
        lang_opts: &'src crate::lang_options::LangOptions,
    ) -> Self {
        Parser {
            lexer,
            current_idx: 0,
            ast,
            lang_opts,
            token_cache: Vec::new(),
            type_context: TypeDefContext::new(),
            keywords: ParserKeywords::new(),
            in_enum_underlying_type: false,
        }
    }

    /// Access the diagnostic engine via the lexer
    pub(crate) fn diag(&mut self) -> &mut DiagnosticEngine {
        self.lexer.preprocessor.diag
    }

    pub(crate) fn report_error<T: crate::diagnostic::IntoDiagnostic>(&mut self, error: T) {
        let sm = &*self.lexer.preprocessor.sm;
        for diag in error.into_diagnostic() {
            self.lexer.preprocessor.diag.report_streaming(diag, sm);
        }
    }

    /// Get the current token (returns None if at end of input)
    fn try_current_token(&mut self) -> Option<Token> {
        self.ensure_cached(self.current_idx);
        self.token_cache.get(self.current_idx).cloned()
    }

    fn ensure_cached(&mut self, index: usize) {
        while self.token_cache.len() <= index {
            match self.lexer.next_token() {
                Ok(Some(token)) => {
                    self.token_cache.push(token);
                }
                Ok(None) => break,
                Err(e) => {
                    self.report_error(e);
                    let span = self.token_cache.last().map(|t| t.span).unwrap_or_default();
                    self.token_cache.push(Token {
                        kind: TokenKind::EndOfFile,
                        span,
                    });
                    break;
                }
            }
        }
    }

    /// Get the current token (returns error if at end of input)
    fn current_token(&mut self) -> Result<Token, ParseDiag> {
        let idx = self.current_idx;
        self.try_current_token().ok_or_else(|| {
            let span = self
                .token_cache
                .get(idx.saturating_sub(1))
                .map(|token| token.span)
                .unwrap_or_default();
            ParseDiag {
                span,
                kind: ParseError::UnexpectedEof,
            }
        })
    }

    /// Get the current token kind
    fn current_token_kind(&mut self) -> Option<TokenKind> {
        self.try_current_token().map(|t| t.kind)
    }

    /// Get the current token location
    pub(super) fn current_token_span(&mut self) -> Result<SourceSpan, ParseDiag> {
        Ok(self.current_token()?.span)
    }

    /// Get the current token location (infallible, returns empty span on EOF)
    pub(super) fn current_token_span_or_empty(&mut self) -> SourceSpan {
        self.try_current_token().map(|t| t.span).unwrap_or_default()
    }

    /// Get the location of the previous token, or an empty span if not available.
    pub(super) fn previous_token_span(&self) -> SourceSpan {
        self.last_token_span().unwrap_or_default()
    }

    /// Get the span of the last token
    pub(super) fn last_token_span(&self) -> Option<SourceSpan> {
        self.current_idx
            .checked_sub(1)
            .and_then(|i| self.token_cache.get(i))
            .map(|t| t.span)
    }

    /// Get the span of a token at a specific index
    pub(super) fn get_token_span(&mut self, index: usize) -> Option<SourceSpan> {
        self.ensure_cached(index);
        self.token_cache.get(index).map(|token| token.span)
    }

    /// Peek at the next token without consuming it
    fn peek_token(&mut self, next_index: u32) -> Option<Token> {
        let target_idx = self.current_idx + 1 + next_index as usize;
        self.ensure_cached(target_idx);
        self.token_cache.get(target_idx).cloned()
    }

    /// Advance to the next token and return previous token
    fn advance(&mut self) -> Option<Token> {
        self.ensure_cached(self.current_idx);
        let token = self.token_cache.get(self.current_idx).cloned()?;
        self.current_idx += 1;
        Some(token)
    }

    /// Accept a specific token kind if found, consume it and return it, otherwise nothing happens
    fn accept(&mut self, accepted: TokenKind) -> Option<Token> {
        if self.current_token_kind() == Some(accepted) {
            self.advance()
        } else {
            None
        }
    }

    /// Expect a specific token kind, consume it if found
    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParseDiag> {
        match self.current_token() {
            Ok(token) => {
                if token.kind == expected {
                    self.advance();
                    Ok(token)
                } else {
                    Err(ParseDiag {
                        span: token.span,
                        kind: ParseError::UnexpectedToken {
                            expected: expected.display(),
                            found: token.kind,
                        },
                    })
                }
            }
            Err(e) => Err(ParseDiag {
                span: e.span,
                kind: ParseError::UnexpectedToken {
                    expected: expected.display(),
                    found: TokenKind::EndOfFile,
                },
            }),
        }
    }

    /// Check if current token matches any of the given kinds
    fn matches(&mut self, kinds: &[TokenKind]) -> bool {
        self.current_token_kind().map(|k| kinds.contains(&k)).unwrap_or(false)
    }

    /// Check if current token matches the given kind
    fn is_token(&mut self, kind: TokenKind) -> bool {
        self.current_token_kind() == Some(kind)
    }

    /// Check if we are at the end of the token stream
    fn at_eof(&mut self) -> bool {
        self.current_token_kind().is_none_or(|k| k == TokenKind::EndOfFile)
    }

    /// Skip tokens until we find a synchronization point.
    /// Default behavior: skip aggressively until `;` at depth 0, unmatched delimiter, or EOF.
    fn synchronize(&mut self) {
        self.synchronize_until(&[]);
    }

    /// Skip tokens until we find a synchronization point, but stop **before** any
    /// token in `stop_before` when at balanced depth. This lets the caller's loop
    /// see the delimiter it needs (e.g. `}` for compound statements).
    fn synchronize_until(&mut self, stop_before: &[TokenKind]) {
        let mut brace_depth: i32 = 0;
        let mut paren_depth: i32 = 0;

        while let Some(token) = self.try_current_token() {
            // If we're at balanced depth and the current token is one the caller
            // wants to handle, stop WITHOUT consuming it.
            if brace_depth <= 0 && paren_depth <= 0 && stop_before.contains(&token.kind) {
                break;
            }

            match token.kind {
                TokenKind::LeftBrace => {
                    brace_depth += 1;
                    self.advance();
                }
                TokenKind::RightBrace => {
                    brace_depth -= 1;
                    self.advance();
                    if brace_depth < 0 {
                        break; // Unmatched brace, stop here
                    }
                }
                TokenKind::LeftParen => {
                    paren_depth += 1;
                    self.advance();
                }
                TokenKind::RightParen => {
                    paren_depth -= 1;
                    self.advance();
                    if paren_depth < 0 {
                        break; // Unmatched paren, stop here
                    }
                }
                TokenKind::Semicolon => {
                    self.advance();
                    if brace_depth == 0 && paren_depth == 0 {
                        break;
                    }
                }
                TokenKind::EndOfFile => {
                    self.advance();
                    break;
                }
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Main expression parsing using Pratt algorithm
    pub(super) fn parse_expression(
        &mut self,
        min_binding_power: expressions::BindingPower,
    ) -> Result<ParsedNodeRef, ParseDiag> {
        parse_expression(self, min_binding_power)
    }

    /// Parse expression with minimum binding power
    pub(super) fn parse_expr_min(&mut self) -> Result<ParsedNodeRef, ParseDiag> {
        self.parse_expression(BindingPower::MIN)
    }

    /// Parse expression up to assignment
    pub(super) fn parse_expr_assignment(&mut self) -> Result<ParsedNodeRef, ParseDiag> {
        self.parse_expression(BindingPower::ASSIGNMENT)
    }

    /// Parse translation unit (top level)
    pub(crate) fn parse_translation_unit(&mut self) -> Result<ParsedNodeRef, ParseDiag> {
        declarations::parse_translation_unit(self)
    }

    /// Disambiguates between a type name and an identifier in ambiguous contexts.
    /// This is crucial for parsing C's "declaration-specifier-list" vs "expression" ambiguity.
    fn is_type_name(&self, symbol: NameId) -> bool {
        self.type_context.is_type_name(symbol)
    }

    /// Check if the given token can start a type name.
    pub(super) fn is_type_name_start_token(&self, token: Token) -> bool {
        match token.kind {
            TokenKind::Attribute => true,
            TokenKind::Identifier(symbol) => self.is_type_name(symbol),
            kind => kind.is_type_specifier() || kind.is_type_qualifier(),
        }
    }

    /// Check if the current token can start a type name.
    /// This is a lightweight check used for disambiguation.
    pub(super) fn is_type_name_start(&mut self) -> bool {
        if self.at_c23_attribute_start() {
            return true;
        }
        self.try_current_token()
            .is_some_and(|token| self.is_type_name_start_token(token))
    }

    /// parse and accept an identifier name
    fn accept_name(&mut self) -> Option<NameId> {
        if let Some(TokenKind::Identifier(symbol)) = self.current_token_kind() {
            self.advance();
            return Some(symbol);
        }
        None
    }

    /// expect and accept an identifier name, returning the symbol or error
    fn expect_name(&mut self) -> Result<(NameId, SourceSpan), ParseDiag> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(symbol) = token.kind {
            self.advance();
            Ok((symbol, token.span))
        } else {
            Err(ParseDiag {
                span: token.span,
                kind: ParseError::UnexpectedToken {
                    expected: "identifier",
                    found: token.kind,
                },
            })
        }
    }

    /// expect and accept a string literal, returning the literal or error
    fn expect_string_literal(&mut self) -> Result<(LitRef, SourceSpan), ParseDiag> {
        let token = self.current_token()?;
        if let TokenKind::Literal(lit) = token.kind
            && lit.kind() == LitKind::String
        {
            self.advance();
            Ok((lit, token.span))
        } else {
            Err(ParseDiag {
                span: token.span,
                kind: ParseError::UnexpectedToken {
                    expected: "string literal",
                    found: token.kind,
                },
            })
        }
    }

    /// Add a typedef name to the type context
    pub(super) fn add_typedef(&mut self, symbol: NameId) {
        self.type_context.add_typedef(symbol);
    }

    fn save_state(&mut self) -> ParserState {
        let diag_len = self.diag().diagnostics.len();
        ParserState {
            current_idx: self.current_idx,
            diag_len,
            type_context_last_scope_len: self.type_context.get_last_scope_len(),
        }
    }

    fn restore_state(&mut self, state: ParserState) {
        self.current_idx = state.current_idx;
        self.diag().diagnostics.truncate(state.diag_len);
        self.type_context.truncate_last_scope(state.type_context_last_scope_len);
    }

    pub(crate) fn start_transaction(&mut self) -> utils::ParserTransaction<'_, 'arena, 'src, 'lexer> {
        utils::ParserTransaction::new(self)
    }

    /// Check if the current token can start a declaration
    pub(super) fn starts_declaration(&mut self) -> bool {
        if self.at_c23_attribute_start() {
            return true;
        }
        self.try_current_token().is_some_and(|token| {
            let is_typedef = matches!(token.kind, TokenKind::Identifier(s) if self.is_type_name(s));
            token.kind.is_declaration_start(is_typedef)
        })
    }

    pub(super) fn at_c23_attribute_start(&mut self) -> bool {
        self.lang_opts.c_standard >= CStandard::C23
            && self.is_token(TokenKind::LeftBracket)
            && self.peek_token(0).is_some_and(|t| t.kind == TokenKind::LeftBracket)
    }

    /// Skip attributes (both GCC and C23)
    pub(super) fn skip_attributes(&mut self) -> Result<(), ParseDiag> {
        while self.is_token(TokenKind::Attribute) || self.at_c23_attribute_start() {
            if self.is_token(TokenKind::Attribute) {
                declarations::parse_attribute(self)?;
            } else {
                declarations::parse_c23_attribute(self)?;
            }
        }
        Ok(())
    }

    /// Parse attributes and return them, breaking the loop on the first error instead of failing.
    /// This is used for error recovery in struct parsing.
    pub(super) fn parse_attributes_lenient(&mut self) -> Vec<crate::ast::parsed::DeclSpec> {
        let mut specs = Vec::new();
        while self.is_token(TokenKind::Attribute) || self.at_c23_attribute_start() {
            if self.is_token(TokenKind::Attribute) {
                if let Ok(attrs) = declarations::parse_attribute(self) {
                    specs.extend(attrs);
                } else {
                    break;
                }
            } else {
                if let Ok(attrs) = declarations::parse_c23_attribute(self) {
                    specs.extend(attrs);
                } else {
                    break;
                }
            }
        }
        specs
    }
}

/// contain functions related to AST nodes
impl<'arena, 'src, 'lexer> Parser<'arena, 'src, 'lexer> {
    /// Push a node to the AST and return its reference
    #[inline]
    pub(super) fn push_node(&mut self, kind: ParsedNodeKind, span: SourceSpan) -> ParsedNodeRef {
        self.ast.push_node(ParsedNode::new(kind, span))
    }

    #[inline]
    pub(super) fn push_dummy(&mut self) -> ParsedNodeRef {
        self.push_node(ParsedNodeKind::Dummy, SourceSpan::empty())
    }

    /// Push a node to the AST and return its reference
    #[inline]
    pub(super) fn replace_node(&mut self, old: ParsedNodeRef, kind: ParsedNodeKind, span: SourceSpan) -> ParsedNodeRef {
        self.ast.replace_node(old, ParsedNode::new(kind, span))
    }

    /// Push Declarator node to AST arena
    #[inline]
    pub(super) fn alloc_decl(&mut self, declarator: ParsedDeclarator) -> DeclaratorRef {
        self.ast.parsed_types.alloc_decl(declarator)
    }

    /// Push BaseType node to AST arena
    #[inline]
    pub(super) fn alloc_base_type(&mut self, base_type: ParsedBaseType) -> ParsedBaseTypeRef {
        self.ast.parsed_types.alloc_base_type(base_type)
    }

    /// Allocate function parameters and return the range
    #[inline]
    pub(super) fn alloc_params(&mut self, params: Vec<crate::ast::ParsedParam>) -> ParsedParamRange {
        self.ast.parsed_types.alloc_params(params)
    }

    /// Allocate struct members and return the range
    #[inline]
    pub(super) fn alloc_struct_members(&mut self, members: Vec<ParsedStructMember>) -> ParsedStructMemberRange {
        self.ast.parsed_types.alloc_struct_members(members)
    }

    /// Allocate enum constants and return the range
    #[inline]
    pub(super) fn alloc_enum_constants(&mut self, enumerators: Vec<ParsedEnumConstant>) -> ParsedEnumRange {
        self.ast.parsed_types.alloc_enum_constants(enumerators)
    }
}
