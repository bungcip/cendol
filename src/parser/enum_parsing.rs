//! Enum parsing module
//!
//! This module handles parsing of enum declarations and enumerators.

use super::Parser;
use crate::ast::*;
use crate::parser::{ParseDiag, TokenKind};

/// Parse enum specifier
pub(super) fn parse_enum_spec(parser: &mut Parser) -> Result<TypeSpec, ParseDiag> {
    let tag = parser.accept_name();

    let original_in_underlying = parser.in_enum_underlying_type;
    let underlying_type = if parser.is_token(TokenKind::Colon)
        && parser.peek_token(0).is_some_and(|t| parser.is_type_name_start_token(t))
    {
        parser.advance();
        parser.in_enum_underlying_type = true;
        let ty = super::type_builder::parse_type_name(parser)?;
        parser.in_enum_underlying_type = original_in_underlying;
        Some(ty)
    } else {
        None
    };

    let enumerators = if !parser.in_enum_underlying_type && parser.accept(TokenKind::LeftBrace).is_some() {
        let enums = parse_enumerator_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;
        Some(enums)
    } else {
        None
    };

    Ok(TypeSpec::Enum(tag, enumerators, underlying_type))
}

/// Parse enumerator list
fn parse_enumerator_list(parser: &mut Parser) -> Result<Vec<ParsedNodeRef>, ParseDiag> {
    crate::parser::utils::parse_comma_separated_list(parser, TokenKind::RightBrace, parse_enumerator)
}

/// Parse enumerator
fn parse_enumerator(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let (name, mut span) = parser.expect_name()?;
    let value = if parser.accept(TokenKind::Assign).is_some() {
        let expr = parser.parse_expr_assignment()?;
        span = span.merge(parser.ast.get_node(expr).span);
        Some(expr)
    } else {
        None
    };

    let node = parser.push_node(ParsedNodeKind::EnumConstant(name, value), span);
    Ok(node)
}
