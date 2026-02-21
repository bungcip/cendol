//! Common parsing utilities and helper functions
//!
//! This module provides utility functions that abstract repetitive patterns
//! found throughout the parser, including expression result handling,
//! binding power utilities, and common parsing operations.

use crate::ast::*;
use crate::diagnostic::ParseError;

use super::expressions::BindingPower;
use super::{Parser, ParserState, TokenKind};

/// Common expression parsing patterns
pub(crate) mod expr_patterns {
    use super::*;

    /// Parse a parenthesized expression: (expression)
    pub(crate) fn parse_parenthesized_expr(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
        parser.expect(TokenKind::LeftParen)?;
        let expr = parser.parse_expr_min()?;
        parser.expect(TokenKind::RightParen)?;
        Ok(expr)
    }

    /// Parse a comma-separated list of expressions with specified binding power
    pub(crate) fn parse_expr_list(
        parser: &mut Parser,
        binding_power: BindingPower,
    ) -> Result<Vec<ParsedNodeRef>, ParseError> {
        let mut args = Vec::new();
        if parser.is_token(TokenKind::RightParen) {
            return Ok(args);
        }

        loop {
            args.push(parser.parse_expression(binding_power)?);
            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
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
