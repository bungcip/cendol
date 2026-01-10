//! Type specifier parsing module
//!
//! This module handles parsing of C type specifiers including basic types,
//! typedef names, struct/union/enum specifiers, and atomic types.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;

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
    let token = parser.try_current_token().ok_or_else(|| ParseError::UnexpectedEof {
        span: parser.previous_token_span(),
    })?;

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
            if let Some(next_token) = parser.try_current_token() {
                match next_token.kind {
                    TokenKind::Long => {
                        parser.advance();
                        Ok(ParsedTypeSpecifier::LongLong)
                    }
                    TokenKind::Double => {
                        parser.advance();
                        Ok(ParsedTypeSpecifier::LongDouble)
                    }
                    _ => Ok(ParsedTypeSpecifier::Long),
                }
            } else {
                Ok(ParsedTypeSpecifier::Long)
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
            // Parse optional base type for _Complex (C11 allows _Complex float, _Complex double, etc.)
            // For now, just consume the base type - full implementation would create proper type
            if parser.accept(TokenKind::Float).is_some()
                || parser.accept(TokenKind::Double).is_some()
                || parser.accept(TokenKind::Long).is_some()
            {
                // For now, just consume the base type - full implementation would create proper type
                if parser.accept(TokenKind::Double).is_some() {
                    // consume double for long double
                }
            }
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
        _ => {
            let expected = "void, char, short, int, long, float, double, signed, unsigned, bool, complex, atomic, struct, union, enum, or identifier";
            Err(ParseError::UnexpectedToken {
                expected_tokens: expected.to_string(),
                found: token.kind,
                span: token.span,
            })
        }
    }
}
