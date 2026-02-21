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
    use ParsedTypeSpecifier as PTS;
    use TokenKind as TK;

    let token = parser.current_token()?;
    match token.kind {
        TK::Void
        | TK::Char
        | TK::Short
        | TK::Int
        | TK::Float
        | TK::Double
        | TK::Signed
        | TK::Unsigned
        | TK::Bool
        | TK::Complex
        | TK::BuiltinVaList => {
            parser.advance();
            Ok(match token.kind {
                TK::Void => PTS::Void,
                TK::Char => PTS::Char,
                TK::Short => PTS::Short,
                TK::Int => PTS::Int,
                TK::Float => PTS::Float,
                TK::Double => PTS::Double,
                TK::Signed => PTS::Signed,
                TK::Unsigned => PTS::Unsigned,
                TK::Bool => PTS::Bool,
                TK::Complex => PTS::Complex,
                TK::BuiltinVaList => PTS::VaList,
                _ => unreachable!(),
            })
        }
        TK::Long => {
            parser.advance();
            match parser.current_token_kind() {
                Some(TK::Long) => {
                    parser.advance();
                    Ok(PTS::LongLong)
                }
                Some(TK::Double) => {
                    parser.advance();
                    Ok(PTS::LongDouble)
                }
                _ => Ok(PTS::Long),
            }
        }
        TK::Struct | TK::Union => {
            parser.advance();
            let is_union = token.kind == TK::Union;
            super::struct_parsing::parse_record_specifier_with_context(parser, is_union, in_struct_member)
        }
        TK::Enum => {
            parser.advance();
            super::enum_parsing::parse_enum_specifier(parser)
        }
        TK::Identifier(symbol) => {
            parser.advance();
            Ok(PTS::TypedefName(symbol))
        }
        _ => unreachable!("ICE: Token {:?} should have been validated", token.kind),
    }
}
