//! Parser module for C11 compiler
//!
//! This module provides the main parser coordination, public API, and state management.
//! It orchestrates the parsing process by delegating to specialized sub-modules for
//! different language constructs.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, ParseError};
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use std::collections::HashSet;

pub mod declaration_core;
pub mod declarations;
pub mod declarator;
pub mod enum_parsing;
pub mod expressions;
pub mod parsed_type_builder;
pub mod statements;
pub mod struct_parsing;
#[cfg(test)]
mod tests_declarations;
pub mod type_specifiers;
pub mod utils;

// Re-export commonly used types
pub(crate) use expressions::BindingPower;

use expressions::parse_expression;

/// Type context for tracking typedef names and other type-related state
#[derive(Debug)]
pub(crate) struct TypeDefContext {
    /// Set of typedef names for disambiguation
    typedef_names: HashSet<NameId>,
}

impl Default for TypeDefContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeDefContext {
    /// Create a new type context with builtin typedefs
    pub(crate) fn new() -> Self {
        let mut typedef_names = HashSet::new();
        // Add builtin typedefs
        typedef_names.insert(NameId::new("va_list"));
        typedef_names.insert(NameId::new("size_t"));
        typedef_names.insert(NameId::new("ptrdiff_t"));
        typedef_names.insert(NameId::new("int8_t"));
        typedef_names.insert(NameId::new("int16_t"));
        typedef_names.insert(NameId::new("int32_t"));
        typedef_names.insert(NameId::new("int64_t"));
        typedef_names.insert(NameId::new("uint8_t"));
        typedef_names.insert(NameId::new("uint16_t"));
        typedef_names.insert(NameId::new("uint32_t"));
        typedef_names.insert(NameId::new("uint64_t"));
        typedef_names.insert(NameId::new("intptr_t"));
        typedef_names.insert(NameId::new("uintptr_t"));

        TypeDefContext { typedef_names }
    }

    /// Check if a symbol is a typedef name
    pub(crate) fn is_type_name(&self, symbol: NameId) -> bool {
        let result = self.typedef_names.contains(&symbol);
        debug!("is_type_name({:?}) = {}", symbol, result);
        result
    }

    /// Add a typedef name
    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        self.typedef_names.insert(symbol);
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ParserState {
    current_idx: usize,
    diag_len: usize,
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
    pub fn new(tokens: &'src [Token], ast: &'arena mut ParsedAst, diag: &'src mut DiagnosticEngine) -> Self {
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
            let prev = self.tokens.get(self.current_idx - 1);
            let span = match prev {
                Some(token) => token.span,
                None => SourceSpan::empty(),
            };
            ParseError::UnexpectedEof { span }
        })
    }

    /// Get the current token kind
    fn current_token_kind(&self) -> Option<TokenKind> {
        self.try_current_token().map(|t| t.kind)
    }

    /// Get the current token location
    pub(crate) fn current_token_span(&self) -> Result<SourceSpan, ParseError> {
        Ok(self.current_token()?.span)
    }

    /// Get the current token location (infallible, returns empty span on EOF)
    pub(crate) fn current_token_span_or_empty(&self) -> SourceSpan {
        self.try_current_token().map(|t| t.span).unwrap_or_default()
    }

    /// Get the location of the previous token, or an empty span if not available.
    pub(crate) fn previous_token_span(&self) -> SourceSpan {
        if self.current_idx > 0 {
            self.tokens
                .get(self.current_idx - 1)
                .map_or(SourceSpan::empty(), |token| token.span)
        } else {
            SourceSpan::empty()
        }
    }

    /// Get the span of the last token (synonym for previous_token_span)
    pub(crate) fn last_token_span(&self) -> Option<SourceSpan> {
        if self.current_idx > 0 {
            self.tokens.get(self.current_idx - 1).map(|token| token.span)
        } else {
            None
        }
    }

    /// Get the span of a token at a specific index
    pub(crate) fn get_token_span(&self, index: usize) -> Option<SourceSpan> {
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
            Err(ParseError::UnexpectedToken {
                expected_tokens: format!("{:?}", expected),
                found: token.kind,
                span: token.span,
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

    /// Skip tokens until we find a synchronization point
    fn synchronize(&mut self) {
        let mut brace_depth = 0;
        let mut paren_depth = 0;
        let mut any_advance = false;

        while let Some(token) = self.try_current_token() {
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

        // If we didn't advance at all, force advance to avoid infinite loop
        if !any_advance {
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
    pub(crate) fn parse_expr_min(&mut self) -> Result<ParsedNodeRef, ParseError> {
        self.parse_expr_bp(BindingPower::MIN)
    }

    /// Parse expression up to assignment
    pub(crate) fn parse_expr_assignment(&mut self) -> Result<ParsedNodeRef, ParseError> {
        self.parse_expr_bp(BindingPower::ASSIGNMENT)
    }

    /// Parse translation unit (top level)
    pub fn parse_translation_unit(&mut self) -> Result<ParsedNodeRef, ParseError> {
        declarations::parse_translation_unit(self)
    }

    /// Check if current token starts an abstract declarator
    fn is_abstract_declarator_start(&self) -> bool {
        declarator::is_abstract_declarator_start(self)
    }

    /// Extract the declared name from a declarator, if any
    fn get_declarator_name(&self, declarator: &crate::ast::parsed::ParsedDeclarator) -> Option<NameId> {
        declarator::get_declarator_name(declarator)
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

    /// Check if the current token can start a type name.
    /// This is a lightweight check used for disambiguation.
    pub(crate) fn is_type_name_start(&self) -> bool {
        if let Some(token) = self.try_current_token() {
            match token.kind {
                // Basic type specifiers
                TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                // Struct/union/enum specifiers
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum
                // Type qualifiers that can start a type name
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic
                // GCC attribute extension
                | TokenKind::Attribute => true,
                // Check for typedef'd identifiers
                TokenKind::Identifier(symbol) => self.is_type_name(symbol),
                _ => false,
            }
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
        if let Some(token) = self.try_current_token()
            && let TokenKind::Identifier(symbol) = token.kind
        {
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
            Err(ParseError::UnexpectedToken {
                expected_tokens: "identifier".to_string(),
                found: token.kind,
                span: token.span,
            })
        }
    }

    /// Add a typedef name to the type context
    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        debug!("add_typedef: adding {:?} to typedef_names", symbol);
        self.type_context.add_typedef(symbol);
    }

    fn save_state(&self) -> ParserState {
        ParserState {
            current_idx: self.current_idx,
            diag_len: self.diag.diagnostics.len(),
        }
    }

    fn restore_state(&mut self, state: ParserState) {
        self.current_idx = state.current_idx;
        self.diag.diagnostics.truncate(state.diag_len);
    }

    pub(crate) fn start_transaction(&mut self) -> utils::ParserTransaction<'_, 'arena, 'src> {
        utils::ParserTransaction::new(self)
    }

    /// Check if the current token can start a declaration
    pub(crate) fn starts_declaration(&self) -> bool {
        if let Some(token) = self.try_current_token() {
            let is_typedef = if let TokenKind::Identifier(symbol) = token.kind {
                self.is_type_name(symbol)
            } else {
                false
            };
            token.kind.is_declaration_start(is_typedef)
        } else {
            false
        }
    }
}

/// contain functions related to AST nodes
impl<'arena, 'src> Parser<'arena, 'src> {
    /// Push a node to the AST and return its reference
    pub(crate) fn push_node(&mut self, kind: ParsedNodeKind, span: SourceSpan) -> ParsedNodeRef {
        self.ast.push_node(ParsedNode::new(kind, span))
    }

    pub(crate) fn push_dummy(&mut self) -> ParsedNodeRef {
        self.push_node(ParsedNodeKind::Dummy, SourceSpan::empty())
    }

    /// Push a node to the AST and return its reference
    pub(crate) fn replace_node(
        &mut self,
        old_ref: ParsedNodeRef,
        kind: ParsedNodeKind,
        span: SourceSpan,
    ) -> ParsedNodeRef {
        self.ast.replace_node(old_ref, ParsedNode::new(kind, span))
    }
}
