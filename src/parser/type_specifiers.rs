//! Type specifier parsing module
//!
//! This module handles parsing of C type specifiers including basic types,
//! typedef names, struct/union/enum specifiers, and atomic types.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::parser::TokenKind;

use super::Parser;

/// Parse type specifier
pub(crate) fn parse_type_specifier(parser: &mut Parser) -> Result<ParsedTypeSpecifier, ParseError> {
    parse_type_specifier_with_context(parser, false)
}

/// Parse type specifier with context
fn parse_type_specifier_with_context(
    parser: &mut Parser,
    in_struct_member: bool,
) -> Result<ParsedTypeSpecifier, ParseError> {
    let token = parser.current_token()?;

    match token.kind {
        TokenKind::Void => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Void)
        }
        TokenKind::Char => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Char)
        }
        TokenKind::Short => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Short)
        }
        TokenKind::Int => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Int)
        }
        TokenKind::Long => {
            parser.advance();
            // Check for long long or long double
            match parser.current_token_kind() {
                Some(TokenKind::Long) => {
                    parser.advance();
                    Ok(ParsedTypeSpecifier::LongLong)
                }
                Some(TokenKind::Double) => {
                    parser.advance();
                    Ok(ParsedTypeSpecifier::LongDouble)
                }
                _ => Ok(ParsedTypeSpecifier::Long),
            }
        }
        TokenKind::Float => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Float)
        }
        TokenKind::Double => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Double)
        }
        TokenKind::Signed => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Signed)
        }
        TokenKind::Unsigned => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Unsigned)
        }
        TokenKind::Bool => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Bool)
        }
        TokenKind::Complex => {
            parser.advance();
            Ok(ParsedTypeSpecifier::Complex)
        }
        TokenKind::Struct => {
            parser.advance();
            super::struct_parsing::parse_record_specifier_with_context(parser, false, in_struct_member)
        }
        TokenKind::Union => {
            parser.advance();
            super::struct_parsing::parse_record_specifier_with_context(parser, true, in_struct_member)
        }
        TokenKind::Enum => {
            parser.advance();
            super::enum_parsing::parse_enum_specifier(parser)
        }
        TokenKind::Identifier(symbol) => {
            parser.advance();
            Ok(ParsedTypeSpecifier::TypedefName(symbol))
        }
        TokenKind::BuiltinVaList => {
            parser.advance();
            Ok(ParsedTypeSpecifier::VaList)
        }
        _ => unreachable!(
            "ICE: Token {:?} should have been validated as a type specifier by the caller",
            token.kind
        ),
    }
}
