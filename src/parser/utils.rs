//! Common parsing utilities and helper functions
//!
//! This module provides utility functions that abstract repetitive patterns
//! found throughout the parser, including expression result handling,
//! binding power utilities, and common parsing operations.

use crate::ast::*;
use crate::diagnostic::ParseError;
use log::debug;

use super::expressions::BindingPower;
use super::{Parser, ParserState};

/// Extension trait for Parser to add utility methods
pub(crate) trait ParserExt {
    /// Check if current token starts a type name
    fn is_type_name_start(&self) -> bool;
}

impl<'arena, 'src> ParserExt for Parser<'arena, 'src> {
    fn is_type_name_start(&self) -> bool {
        debug!(
            "is_type_name_start: checking token {:?} at position {}",
            self.current_token_kind(),
            self.current_idx
        );

        if let Some(token) = self.try_current_token() {
            let is_specifier = token.kind.is_type_specifier() || token.kind.is_type_qualifier();

            let is_identifier_type = if let crate::lexer::TokenKind::Identifier(symbol) = token.kind {
                self.is_type_name(symbol)
            } else {
                false
            };

            let final_result = is_specifier || is_identifier_type;
            debug!(
                "is_type_name_start: token {:?} is type name start: {} (specifier: {}, identifier: {})",
                token.kind, final_result, is_specifier, is_identifier_type
            );
            final_result
        } else {
            debug!("is_type_name_start: no token available");
            false
        }
    }
}

/// Common expression parsing patterns
pub(crate) mod expr_patterns {
    use super::*;

    /// Parse a parenthesized expression: (expression)
    pub(crate) fn parse_parenthesized_expr(parser: &mut Parser) -> Result<NodeRef, ParseError> {
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
    ) -> Result<Vec<NodeRef>, ParseError> {
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
