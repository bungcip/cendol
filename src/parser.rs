//! Parser module for C11 compiler
//!
//! This module provides the main parser coordination, public API, and state management.
//! It orchestrates the parsing process by delegating to specialized sub-modules for
//! different language constructs.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, ParseError, ParseErrorKind};
use crate::source_manager::{SourceLoc, SourceSpan};

pub mod declaration_core;
pub mod declarations;
pub mod declarator;
pub mod enum_parsing;
pub mod expressions;
pub mod lexer;
pub mod statements;
pub mod struct_parsing;
pub mod type_builder;
pub mod type_specifiers;
pub mod utils;

// Re-export commonly used types
pub(crate) use expressions::BindingPower;
pub(crate) use lexer::{Lexer, Token, TokenKind};

use expressions::parse_expression;

/// Type context for tracking typedef names and other type-related state
#[derive(Debug)]
pub(crate) struct TypeDefContext {
    /// Stack of scopes, each containing a list of (NameId, is_typedef) for disambiguation
    scopes: Vec<Vec<(NameId, bool)>>,
}

impl TypeDefContext {
    /// Create a new type context with builtin typedefs
    pub(crate) fn new() -> Self {
        let globals = vec![
            (NameId::new("int8_t"), true),
            (NameId::new("int16_t"), true),
            (NameId::new("int32_t"), true),
            (NameId::new("int64_t"), true),
            (NameId::new("uint8_t"), true),
            (NameId::new("uint16_t"), true),
            (NameId::new("uint32_t"), true),
            (NameId::new("uint64_t"), true),
        ];

        TypeDefContext { scopes: vec![globals] }
    }

    /// Check if a symbol is a typedef name
    pub(crate) fn is_type_name(&self, symbol: NameId) -> bool {
        for scope in self.scopes.iter().rev() {
            for &(name, is_typedef) in scope.iter().rev() {
                if name == symbol {
                    return is_typedef;
                }
            }
        }
        false
    }

    /// Add a typedef name
    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push((symbol, true));
    }

    /// Add a non-typedef name (e.g. variable or function) that shadows outer typedefs
    pub(crate) fn add_non_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push((symbol, false));
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn get_last_scope_len(&self) -> usize {
        self.scopes.last().map(|s| s.len()).unwrap_or(0)
    }

    fn truncate_last_scope(&mut self, len: usize) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.truncate(len);
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
pub struct Parser<'arena, 'src> {
    tokens: &'src [Token],
    current_idx: usize,
    ast: &'arena mut ParsedAst,
    diag: &'src mut DiagnosticEngine,

    // Type context for typedef tracking
    type_context: TypeDefContext,
}

impl<'arena, 'src> Parser<'arena, 'src> {
    /// Create a new parser
    pub(crate) fn new(tokens: &'src [Token], ast: &'arena mut ParsedAst, diag: &'src mut DiagnosticEngine) -> Self {
        Parser {
            tokens,
            current_idx: 0,
            ast,
            diag,
            type_context: TypeDefContext::new(),
        }
    }

    /// Get the current token (returns None if at end of input)
    fn try_current_token(&self) -> Option<Token> {
        self.tokens.get(self.current_idx).cloned()
    }

    /// Get the current token (returns error if at end of input)
    fn current_token(&self) -> Result<Token, ParseError> {
        self.try_current_token().ok_or_else(|| {
            let span = self
                .tokens
                .get(self.current_idx.saturating_sub(1))
                .map(|token| token.span)
                .unwrap_or_default();
            ParseError {
                span,
                kind: ParseErrorKind::UnexpectedEof,
            }
        })
    }

    /// Get the current token kind
    fn current_token_kind(&self) -> Option<TokenKind> {
        self.try_current_token().map(|t| t.kind)
    }

    /// Get the current token location
    fn current_token_span(&self) -> Result<SourceSpan, ParseError> {
        Ok(self.current_token()?.span)
    }

    /// Get the current token location (infallible, returns empty span on EOF)
    fn current_token_span_or_empty(&self) -> SourceSpan {
        self.try_current_token().map(|t| t.span).unwrap_or_default()
    }

    /// Get the location of the previous token, or an empty span if not available.
    fn previous_token_span(&self) -> SourceSpan {
        self.last_token_span().unwrap_or_default()
    }

    /// Get the span of the last token
    fn last_token_span(&self) -> Option<SourceSpan> {
        self.current_idx
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map(|t| t.span)
    }

    /// Get the span of a token at a specific index
    fn get_token_span(&self, index: usize) -> Option<SourceSpan> {
        self.tokens.get(index).map(|token| token.span)
    }

    /// Peek at the next token without consuming it
    fn peek_token(&self, next_index: u32) -> Option<&Token> {
        self.tokens.get(self.current_idx + 1 + next_index as usize)
    }

    /// Advance to the next token and return previous token
    fn advance(&mut self) -> Option<Token> {
        if self.current_idx < self.tokens.len() {
            let token = &self.tokens[self.current_idx];
            self.current_idx += 1;
            Some(*token)
        } else {
            None
        }
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
    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParseError> {
        let token = self.current_token()?;
        if token.kind == expected {
            self.advance();
            Ok(token)
        } else {
            Err(ParseError {
                span: token.span,
                kind: ParseErrorKind::UnexpectedToken {
                    expected: expected.display(),
                    found: token.kind,
                },
            })
        }
    }

    /// Check if current token matches any of the given kinds
    fn matches(&self, kinds: &[TokenKind]) -> bool {
        self.current_token_kind().map(|k| kinds.contains(&k)).unwrap_or(false)
    }

    /// Check if current token matches the given kind
    fn is_token(&self, kind: TokenKind) -> bool {
        self.current_token_kind() == Some(kind)
    }

    /// Check if we are at the end of the token stream
    fn at_eof(&self) -> bool {
        self.current_token_kind() == Some(TokenKind::EndOfFile) || self.current_token_kind().is_none()
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
        let mut any_advance = false;
        let mut stopped_at_stop_token = false;

        while let Some(token) = self.try_current_token() {
            // If we're at balanced depth and the current token is one the caller
            // wants to handle, stop WITHOUT consuming it.
            if brace_depth <= 0 && paren_depth <= 0 && stop_before.contains(&token.kind) {
                stopped_at_stop_token = true;
                break;
            }

            match token.kind {
                TokenKind::LeftBrace => {
                    brace_depth += 1;
                    self.advance();
                    any_advance = true;
                }
                TokenKind::RightBrace => {
                    brace_depth -= 1;
                    self.advance();
                    any_advance = true;
                    if brace_depth < 0 {
                        break; // Unmatched brace, stop here
                    }
                }
                TokenKind::LeftParen => {
                    paren_depth += 1;
                    self.advance();
                    any_advance = true;
                }
                TokenKind::RightParen => {
                    paren_depth -= 1;
                    self.advance();
                    any_advance = true;
                    if paren_depth < 0 {
                        break; // Unmatched paren, stop here
                    }
                }
                TokenKind::Semicolon => {
                    self.advance();
                    any_advance = true;
                    if brace_depth == 0 && paren_depth == 0 {
                        break;
                    }
                }
                TokenKind::EndOfFile => {
                    self.advance();
                    any_advance = true;
                    break;
                }
                _ => {
                    self.advance();
                    any_advance = true;
                }
            }
        }

        // Force advance only if we didn't advance AND didn't stop at a designated stop token
        if !any_advance && !stopped_at_stop_token {
            self.advance();
        }
    }

    /// Main expression parsing using Pratt algorithm
    pub(crate) fn parse_expression(
        &mut self,
        min_binding_power: expressions::BindingPower,
    ) -> Result<ParsedNodeRef, ParseError> {
        parse_expression(self, min_binding_power)
    }

    /// Private helper to parse an expression with a given binding power, ensuring it's not a declaration.
    fn parse_expr_bp(&mut self, min_binding_power: BindingPower) -> Result<ParsedNodeRef, ParseError> {
        self.parse_expression(min_binding_power)
    }

    /// Parse expression with minimum binding power
    fn parse_expr_min(&mut self) -> Result<ParsedNodeRef, ParseError> {
        self.parse_expr_bp(BindingPower::MIN)
    }

    /// Parse expression up to assignment
    fn parse_expr_assignment(&mut self) -> Result<ParsedNodeRef, ParseError> {
        self.parse_expr_bp(BindingPower::ASSIGNMENT)
    }

    /// Parse translation unit (top level)
    pub(crate) fn parse_translation_unit(&mut self) -> Result<ParsedNodeRef, ParseError> {
        declarations::parse_translation_unit(self)
    }

    /// Check if current token starts an abstract declarator
    fn is_abstract_declarator_start(&self) -> bool {
        declarator::is_abstract_declarator_start(self)
    }

    /// Extract the declared name from a declarator, if any
    fn get_declarator_name(&self, declarator: DeclaratorRef) -> Option<NameId> {
        declarator::get_declarator_name(&self.ast.parsed_types, declarator)
    }

    /// Disambiguates between a type name and an identifier in ambiguous contexts.
    /// This is crucial for parsing C's "declaration-specifier-list" vs "expression" ambiguity.
    fn is_type_name(&self, symbol: NameId) -> bool {
        self.type_context.is_type_name(symbol)
    }

    /// Check if a cast expression starts at the current position
    /// This is called after consuming an opening parenthesis
    fn is_cast_expression_start(&self) -> bool {
        expressions::is_cast_expression_start(self)
    }

    /// Check if the given token can start a type name.
    fn is_type_name_start_token(&self, token: &Token) -> bool {
        match token.kind {
            TokenKind::Attribute => true,
            TokenKind::Identifier(symbol) => self.is_type_name(symbol),
            kind => kind.is_type_specifier() || kind.is_type_qualifier(),
        }
    }

    /// Check if the current token can start a type name.
    /// This is a lightweight check used for disambiguation.
    fn is_type_name_start(&self) -> bool {
        if let Some(token) = self.try_current_token() {
            self.is_type_name_start_token(&token)
        } else {
            false
        }
    }

    /// Parse cast expression given the already parsed type and right paren token
    fn parse_cast_expression_from_type_and_paren(
        &mut self,
        parsed_type: ParsedType,
        right_paren_token: Token,
    ) -> Result<ParsedNodeRef, ParseError> {
        expressions::parse_cast_expression_from_type_and_paren(self, parsed_type, right_paren_token)
    }

    /// Parse compound literal given the type and start location
    fn parse_compound_literal_from_type_and_start(
        &mut self,
        parsed_type: ParsedType,
        start_loc: SourceLoc,
    ) -> Result<ParsedNodeRef, ParseError> {
        expressions::parse_compound_literal_from_type_and_start(self, parsed_type, start_loc)
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
    fn expect_name(&mut self) -> Result<(NameId, SourceSpan), ParseError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(symbol) = token.kind {
            self.advance();
            Ok((symbol, token.span))
        } else {
            Err(ParseError {
                span: token.span,
                kind: ParseErrorKind::UnexpectedToken {
                    expected: "identifier",
                    found: token.kind,
                },
            })
        }
    }

    /// Add a typedef name to the type context
    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        self.type_context.add_typedef(symbol);
    }

    fn save_state(&self) -> ParserState {
        ParserState {
            current_idx: self.current_idx,
            diag_len: self.diag.diagnostics.len(),
            type_context_last_scope_len: self.type_context.get_last_scope_len(),
        }
    }

    fn restore_state(&mut self, state: ParserState) {
        self.current_idx = state.current_idx;
        self.diag.diagnostics.truncate(state.diag_len);
        self.type_context.truncate_last_scope(state.type_context_last_scope_len);
    }

    fn start_transaction(&mut self) -> utils::ParserTransaction<'_, 'arena, 'src> {
        utils::ParserTransaction::new(self)
    }

    /// Check if the current token can start a declaration
    fn starts_declaration(&self) -> bool {
        self.try_current_token().is_some_and(|token| {
            let is_typedef = matches!(token.kind, TokenKind::Identifier(s) if self.is_type_name(s));
            token.kind.is_declaration_start(is_typedef)
        })
    }
}

/// contain functions related to AST nodes
impl<'arena, 'src> Parser<'arena, 'src> {
    /// Push a node to the AST and return its reference
    #[inline]
    fn push_node(&mut self, kind: ParsedNodeKind, span: SourceSpan) -> ParsedNodeRef {
        self.ast.push_node(ParsedNode::new(kind, span))
    }

    #[inline]
    fn push_dummy(&mut self) -> ParsedNodeRef {
        self.push_node(ParsedNodeKind::Dummy, SourceSpan::empty())
    }

    /// Push a node to the AST and return its reference
    #[inline]
    fn replace_node(
        &mut self,
        old_ref: ParsedNodeRef,
        kind: ParsedNodeKind,
        span: SourceSpan,
    ) -> ParsedNodeRef {
        self.ast.replace_node(old_ref, ParsedNode::new(kind, span))
    }

    /// Push Declarator node to AST arena
    #[inline]
    fn alloc_decl(&mut self, declarator: ParsedDeclarator) -> DeclaratorRef {
        self.ast.parsed_types.alloc_decl(declarator)
    }

    /// Push BaseType node to AST arena
    #[inline]
    fn alloc_base_type(&mut self, base_type: ParsedBaseType) -> ParsedBaseTypeRef {
        self.ast.parsed_types.alloc_base_type(base_type)
    }

    /// Allocate function parameters and return the range
    #[inline]
    fn alloc_params(&mut self, params: Vec<crate::ast::ParsedParam>) -> ParsedParamRange {
        self.ast.parsed_types.alloc_params(params)
    }

    /// Allocate struct members and return the range
    #[inline]
    fn alloc_struct_members(&mut self, members: Vec<ParsedStructMember>) -> ParsedStructMemberRange {
        self.ast.parsed_types.alloc_struct_members(members)
    }

    /// Allocate enum constants and return the range
    #[inline]
    fn alloc_enum_constants(&mut self, enumerators: Vec<ParsedEnumConstant>) -> ParsedEnumRange {
        self.ast.parsed_types.alloc_enum_constants(enumerators)
    }
}
