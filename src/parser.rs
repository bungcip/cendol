//! Parser module for C11 compiler
//!
//! This module provides the main parser coordination, public API, and state management.
//! It orchestrates the parsing process by delegating to specialized sub-modules for
//! different language constructs.

use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::{CStandard, LangOptions};
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

use crate::semantic::{ScopeId, SymbolClass, SymbolTable};

#[derive(Clone)]
pub(crate) struct ParserState {
    current_idx: usize,
    diag_len: usize,
    error_count: usize,
    warning_count: usize,
    symbol_table_state: crate::semantic::symbol_table::SymbolTableState,
}

/// Main parser structure
pub struct Parser<'arena, 'src, 'lexer> {
    pub(crate) lexer: &'lexer mut Lexer<'src>,
    pub(crate) current_idx: usize,
    pub(crate) ast: PAst,
    pub(crate) lang_opts: &'src LangOptions,

    // Token caching for lookahead and backtracking
    pub(crate) token_cache: Vec<Token>,

    // Symbol table for scope and typedef tracking
    pub(crate) symbol_table: &'arena mut SymbolTable,
    pub(crate) next_compound_uses_scope: Option<ScopeId>,
    pub(crate) keywords: ParserKeywords,

    /// Flag to indicate if we are parsing an enum's underlying type
    pub(crate) in_enum_underlying_type: bool,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ParserKeywords {
    pub(crate) attr_alias: NameId,
    pub(crate) attr_alias_underscore: NameId,
    pub(crate) attr_mode: NameId,
    pub(crate) attr_mode_underscore: NameId,
    pub(crate) attr_noreturn: NameId,
    pub(crate) attr_noreturn_underscore: NameId,
    pub(crate) attr_aligned: NameId,
    pub(crate) attr_aligned_underscore: NameId,
    pub(crate) attr_packed: NameId,
    pub(crate) attr_packed_underscore: NameId,
    pub(crate) attr_cleanup: NameId,
    pub(crate) attr_cleanup_underscore: NameId,
    pub(crate) attr_transparent_union: NameId,
    pub(crate) attr_transparent_union_underscore: NameId,
    pub(crate) attr_visibility: NameId,
    pub(crate) attr_visibility_underscore: NameId,
}

impl ParserKeywords {
    fn new() -> Self {
        ParserKeywords {
            attr_alias: NameId::new("alias"),
            attr_alias_underscore: NameId::new("__alias__"),
            attr_mode: NameId::new("mode"),
            attr_mode_underscore: NameId::new("__mode__"),
            attr_noreturn: NameId::new("noreturn"),
            attr_noreturn_underscore: NameId::new("__noreturn__"),
            attr_aligned: NameId::new("aligned"),
            attr_aligned_underscore: NameId::new("__aligned__"),
            attr_packed: NameId::new("packed"),
            attr_packed_underscore: NameId::new("__packed__"),
            attr_cleanup: NameId::new("cleanup"),
            attr_cleanup_underscore: NameId::new("__cleanup__"),
            attr_transparent_union: NameId::new("transparent_union"),
            attr_transparent_union_underscore: NameId::new("__transparent_union__"),
            attr_visibility: NameId::new("visibility"),
            attr_visibility_underscore: NameId::new("__visibility__"),
        }
    }
}

impl<'arena, 'src, 'lexer> Parser<'arena, 'src, 'lexer> {
    /// Create a new parser
    pub(crate) fn new(
        lexer: &'lexer mut Lexer<'src>,
        symbol_table: &'arena mut SymbolTable,
        lang_opts: &'src LangOptions,
    ) -> Self {
        Parser {
            lexer,
            current_idx: 0,
            ast: PAst::new(),
            lang_opts,
            token_cache: Vec::new(),
            symbol_table,
            next_compound_uses_scope: None,
            keywords: ParserKeywords::new(),
            in_enum_underlying_type: false,
        }
    }

    pub(crate) fn take_ast(self) -> PAst {
        self.ast
    }

    /// Access the diagnostic engine via the lexer
    pub(crate) fn diag(&mut self) -> &mut DiagnosticEngine {
        self.lexer.preprocessor.diag
    }

    pub(crate) fn report_error<T: crate::diagnostic::IntoDiagnostic>(&mut self, error: T) {
        let sm = &*self.lexer.preprocessor.sm;
        for diag in error.into_diagnostic() {
            self.lexer.preprocessor.diag.report(diag, sm);
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
    pub(super) fn parse_expression(&mut self, min_bp: BindingPower) -> Result<PNodeRef, ParseDiag> {
        parse_expression(self, min_bp)
    }

    /// Parse expression with minimum binding power
    pub(super) fn parse_expr_min(&mut self) -> Result<PNodeRef, ParseDiag> {
        self.parse_expression(BindingPower::MIN)
    }

    /// Parse expression up to assignment
    pub(super) fn parse_expr_assignment(&mut self) -> Result<PNodeRef, ParseDiag> {
        self.parse_expression(BindingPower::ASSIGNMENT)
    }

    /// Parse an expression if the current token is not the given `end_token`.
    /// Then expect and consume the `end_token`.
    pub(crate) fn parse_optional_expr_before(&mut self, end_token: TokenKind) -> Result<Option<PNodeRef>, ParseDiag> {
        let expr = (!self.is_token(end_token)).then(|| self.parse_expr_min()).transpose()?;
        self.expect(end_token)?;
        Ok(expr)
    }

    /// Parse translation unit (top level)
    pub(crate) fn parse_translation_unit(&mut self) -> Result<PNodeRef, ParseDiag> {
        declarations::parse_translation_unit(self)
    }

    fn is_type_name(&self, symbol: NameId) -> bool {
        if let Some(sym) = self.symbol_table.lookup_symbol(symbol) {
            sym.class() == SymbolClass::Typedef
        } else {
            false
        }
    }

    /// Check if the given token can start a type name.
    pub(super) fn is_type_name_start_token(&self, kind: &TokenKind) -> bool {
        match kind {
            TokenKind::Attribute => true,
            TokenKind::Identifier(symbol) => self.is_type_name(*symbol),
            _ => kind.is_type_specifier() || kind.is_type_qualifier(),
        }
    }

    /// Check if the current token can start a type name.
    /// This is a lightweight check used for disambiguation.
    pub(super) fn is_type_name_start(&mut self) -> bool {
        if self.at_c23_attribute_start() {
            return true;
        }
        self.try_current_token()
            .is_some_and(|token| self.is_type_name_start_token(&token.kind))
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
    fn expect_string_literal(&mut self) -> Result<(StringLitRef, SourceSpan), ParseDiag> {
        let token = self.current_token()?;
        if let TokenKind::Literal(lit) = token.kind
            && lit.kind() == LitKind::String
        {
            self.advance();
            Ok((StringLitRef::new(lit), token.span))
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
        let span = self.current_token_span_or_empty();
        self.symbol_table.define_parser_typedef(symbol, span);
    }

    fn save_state(&mut self) -> ParserState {
        let current_idx = self.current_idx;
        let symbol_table_state = self.symbol_table.save_state();
        let diag = self.diag();
        ParserState {
            current_idx,
            diag_len: diag.diagnostics.len(),
            error_count: diag.error_count,
            warning_count: diag.warning_count,
            symbol_table_state,
        }
    }

    fn restore_state(&mut self, state: ParserState) {
        self.current_idx = state.current_idx;
        self.symbol_table.restore_state(state.symbol_table_state);
        let diag = self.diag();
        diag.diagnostics.truncate(state.diag_len);
        diag.error_count = state.error_count;
        diag.warning_count = state.warning_count;
    }

    /// Execute a parsing function within a transaction.
    /// If the function returns `Ok`, the transaction is committed.
    /// If it returns `Err`, the transaction is rolled back.
    pub(crate) fn transaction<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Parser<'arena, 'src, 'lexer>) -> Result<T, E>,
    {
        let trx = utils::ParserTransaction::new(self);
        trx.parser.diag().stream_muted += 1;
        match f(trx.parser) {
            Ok(result) => {
                trx.parser.diag().stream_muted -= 1;
                let sm_ptr = trx.parser.lexer.preprocessor.sm as *const _;
                trx.parser.diag().flush_stream(unsafe { &*sm_ptr });
                trx.commit();
                Ok(result)
            }
            Err(e) => {
                trx.parser.diag().stream_muted -= 1;
                // when rolled back, the ParserTransaction Drop impl restores state (and truncates error/warnings)
                Err(e)
            }
        }
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
            let res = if self.is_token(TokenKind::Attribute) {
                declarations::parse_attribute(self)
            } else {
                declarations::parse_c23_attribute(self)
            };
            if let Ok(attrs) = res {
                specs.extend(attrs);
            } else {
                break;
            }
        }
        specs
    }
}

/// contain functions related to AST nodes
impl<'arena, 'src, 'lexer> Parser<'arena, 'src, 'lexer> {
    /// Push a node to the AST and return its reference
    #[inline]
    pub(super) fn push_node(&mut self, kind: PNodeKind, span: SourceSpan) -> PNodeRef {
        self.ast.push_node(PNode::new(kind, span))
    }

    #[inline]
    pub(super) fn push_dummy(&mut self) -> PNodeRef {
        self.push_node(PNodeKind::Dummy, SourceSpan::empty())
    }

    /// Push a node to the AST and return its reference
    #[inline]
    pub(super) fn replace_node(&mut self, old: PNodeRef, kind: PNodeKind, span: SourceSpan) -> PNodeRef {
        self.ast.replace_node(old, PNode::new(kind, span))
    }

    /// Push Declarator node to AST arena
    #[inline]
    pub(super) fn alloc_decl(&mut self, declarator: PDeclarator) -> DeclaratorRef {
        self.ast.parsed_types.alloc_decl(declarator)
    }

    /// Push BaseType node to AST arena
    #[inline]
    pub(super) fn alloc_type_spec(&mut self, type_spec: TypeSpec) -> PTypeSpecRef {
        self.ast.parsed_types.alloc_type_spec(type_spec)
    }

    /// Allocate function parameters and return the range
    #[inline]
    pub(super) fn alloc_params(&mut self, params: Vec<PParam>) -> PParamRange {
        self.ast.parsed_types.alloc_params(params)
    }
}
