//! Enum parsing module
//!
//! This module handles parsing of enum declarations and enumerators.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::source_manager::SourceSpan;
use symbol_table::GlobalSymbol as Symbol;

use super::Parser;
use super::{BindingPower, parse_expression, unwrap_expr_result};

/// Parse enum specifier
pub fn parse_enum_specifier(parser: &mut Parser) -> Result<TypeSpecifier, ParseError> {
    let tag = if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            parser.advance().ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?;
            Some(symbol)
        } else {
            None
        }
    } else {
        None
    };

    let enumerators = if parser.accept(TokenKind::LeftBrace).is_some() {
        let enums = parse_enumerator_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;
        Some(enums)
    } else {
        None
    };

    Ok(TypeSpecifier::Enum(tag, enumerators))
}

/// Parse enumerator list
pub fn parse_enumerator_list(parser: &mut Parser) -> Result<Vec<NodeRef>, ParseError> {
    let mut enumerators = Vec::new();

    loop {
        let enumerator = parse_enumerator(parser)?;
        enumerators.push(enumerator);

        if !parser.is_token(TokenKind::Comma) {
            break;
        }
        parser.advance(); // consume comma

        // Allow trailing comma
        if parser.is_token(TokenKind::RightBrace) {
            break;
        }
    }

    Ok(enumerators)
}

/// Parse enumerator
pub fn parse_enumerator(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let token = parser.try_current_token().ok_or_else(|| ParseError::SyntaxError {
        message: "Expected enumerator name".to_string(),
        location: SourceSpan::empty(),
    })?;

    let name = match token.kind {
        TokenKind::Identifier(symbol) => symbol,
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected: vec![TokenKind::Identifier(Symbol::new(""))],
                found: token.kind,
                location: token.location,
            });
        }
    };

    parser.advance().ok_or_else(|| ParseError::SyntaxError {
        message: "Unexpected end of input".to_string(),
        location: SourceSpan::empty(),
    })?;

    let value = if parser.accept(TokenKind::Assign).is_some() {
        let expr_result = parse_expression(parser, BindingPower::ASSIGNMENT);
        Some(unwrap_expr_result(
            parser,
            expr_result,
            "expression for enumerator value",
        )?)
    } else {
        None
    };

    let span = SourceSpan::new(token.location.start, token.location.end);

    let node = parser.ast.push_node(Node {
        kind: NodeKind::EnumConstant(name, value),
        span,
        resolved_type: std::cell::Cell::new(None),
        resolved_symbol: std::cell::Cell::new(None),
    });
    Ok(node)
}
