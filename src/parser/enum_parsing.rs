//! Enum parsing module
//!
//! This module handles parsing of enum declarations and enumerators.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;

use super::Parser;

/// Parse enum specifier
pub(crate) fn parse_enum_specifier(parser: &mut Parser) -> Result<ParsedTypeSpecifier, ParseError> {
    let tag = parser.accept_name();
    let enumerators = if parser.accept(TokenKind::LeftBrace).is_some() {
        let enums = parse_enumerator_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;
        Some(enums)
    } else {
        None
    };

    Ok(ParsedTypeSpecifier::Enum(tag, enumerators))
}

/// Parse enumerator list
fn parse_enumerator_list(parser: &mut Parser) -> Result<Vec<ParsedNodeRef>, ParseError> {
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
fn parse_enumerator(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let (name, mut span) = parser.expect_name()?;
    let value = if parser.accept(TokenKind::Assign).is_some() {
        let expr = parser.parse_expr_assignment()?;
        span = SourceSpan::new(span.start(), parser.ast.get_node(expr).span.end());
        Some(expr)
    } else {
        None
    };

    let node = parser.push_node(ParsedNodeKind::EnumConstant(name, value), span);
    Ok(node)
}
