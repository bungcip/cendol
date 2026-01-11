//! Common parsing utilities and helper functions
//!
//! This module provides utility functions that abstract repetitive patterns
//! found throughout the parser, including expression result handling,
//! binding power utilities, and common parsing operations.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use log::debug;

use super::expressions::BindingPower;
use super::{Parser, ParserState};

/// Common expression parsing patterns
pub(crate) mod expr_patterns {
    use super::*;

    /// Parse a parenthesized expression: (expression)
    pub(crate) fn parse_parenthesized_expr(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
        debug!("parse_parenthesized_expr: parsing parenthesized expression");
        parser.expect(crate::lexer::TokenKind::LeftParen)?;
        let expr = parser.parse_expr_min()?;
        parser.expect(crate::lexer::TokenKind::RightParen)?;
        Ok(expr)
    }

    /// Parse a comma-separated list of expressions with specified binding power
    pub(crate) fn parse_expr_list(
        parser: &mut Parser,
        binding_power: BindingPower,
    ) -> Result<Vec<ParsedNodeRef>, ParseError> {
        debug!("parse_expr_list: parsing expression list");
        let mut args = Vec::new();

        if parser.is_token(crate::lexer::TokenKind::RightParen) {
            return Ok(args);
        }

        loop {
            let arg = parser.parse_expression(binding_power)?;
            args.push(arg);

            if !parser.is_token(crate::lexer::TokenKind::Comma) {
                break;
            }
            parser.advance(); // consume comma
        }

        Ok(args)
    }
}

pub(crate) struct ParserTransaction<'a, 'arena, 'src> {
    pub(crate) parser: &'a mut Parser<'arena, 'src>,
    state: ParserState,
    committed: bool,
}

impl<'a, 'arena, 'src> ParserTransaction<'a, 'arena, 'src> {
    pub(crate) fn new(parser: &'a mut Parser<'arena, 'src>) -> Self {
        let state = parser.save_state();
        Self {
            parser,
            state,
            committed: false,
        }
    }

    pub(crate) fn commit(mut self) {
        self.committed = true;
    }
}

impl<'a, 'arena, 'src> Drop for ParserTransaction<'a, 'arena, 'src> {
    fn drop(&mut self) {
        if !self.committed {
            self.parser.restore_state(self.state.clone());
        }
    }
}

/// A struct to hold pre-computed classifications for a token.
/// This avoids repeatedly calling classification methods on `TokenKind`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TokenClassification {
    pub is_type_specifier: bool,
    pub is_type_qualifier: bool,
    pub is_storage_class_specifier: bool,
    pub is_function_specifier: bool,
    pub is_alignment_specifier: bool,
    pub is_declaration_specifier_start: bool,
}

impl TokenClassification {
    /// Classify a token kind and return the classification struct.
    ///
    /// ⚡ Bolt: Centralized Token Classification.
    /// This function uses a single, comprehensive `match` statement to classify
    /// a token kind. The results are stored in a struct, allowing parser logic
    /// to query boolean properties directly instead of calling multiple `matches!`-based
    /// functions. This is more efficient as the classification is performed only once
    /// per token lookahead, and the consolidated logic is easier to maintain.
    pub(crate) fn classify(kind: TokenKind) -> Self {
        let mut s = Self {
            is_type_specifier: false,
            is_type_qualifier: false,
            is_storage_class_specifier: false,
            is_function_specifier: false,
            is_alignment_specifier: false,
            is_declaration_specifier_start: false,
        };

        match kind {
            // Storage class specifiers
            TokenKind::Typedef | TokenKind::Extern | TokenKind::Static | TokenKind::ThreadLocal | TokenKind::Auto | TokenKind::Register => {
                s.is_storage_class_specifier = true;
            }
            // Type specifiers
            TokenKind::Void | TokenKind::Char | TokenKind::Short | TokenKind::Int | TokenKind::Long | TokenKind::Float | TokenKind::Double | TokenKind::Signed | TokenKind::Unsigned | TokenKind::Bool | TokenKind::Complex | TokenKind::Struct | TokenKind::Union | TokenKind::Enum => {
                s.is_type_specifier = true;
            }
            // Type qualifiers
            TokenKind::Const | TokenKind::Restrict | TokenKind::Volatile | TokenKind::Atomic => {
                // Note: Atomic is both a specifier and a qualifier
                s.is_type_qualifier = true;
                if kind == TokenKind::Atomic {
                    s.is_type_specifier = true;
                }
            }
            // Function specifiers
            TokenKind::Inline | TokenKind::Noreturn => {
                s.is_function_specifier = true;
            }
            // Alignment specifiers
            TokenKind::Alignas => {
                s.is_alignment_specifier = true;
            }
            _ => {}
        }

        s.is_declaration_specifier_start = s.is_storage_class_specifier
            || s.is_type_specifier
            || s.is_type_qualifier
            || s.is_function_specifier
            || s.is_alignment_specifier
            || matches!(kind, TokenKind::Attribute);

        s
    }
}
