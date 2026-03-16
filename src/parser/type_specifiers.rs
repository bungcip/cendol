//! Type specifier parsing module
//!
//! This module handles parsing of C type specifiers including basic types,
//! typedef names, struct/union/enum specifiers, and atomic types.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::parser::enum_parsing::parse_enum_specifier;
use crate::parser::expressions::parse_expression;
use crate::parser::struct_parsing::parse_record_specifier;
use crate::parser::type_builder::parse_type_name;
use crate::parser::{BindingPower, TokenKind};

use super::Parser;

/// Parse type specifier
pub(super) fn parse_type_specifier(parser: &mut Parser) -> Result<ParsedTypeSpec, ParseError> {
    use ParsedTypeSpec as PTS;
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
        | TK::BuiltinVaList
        | TK::AutoType => {
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
                TK::AutoType => PTS::AutoType,
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
        TK::Typeof => {
            parser.advance();
            parser.expect(TK::LeftParen)?;
            let is_type = parser.is_type_name_start();
            let ts = if is_type {
                let ty = parse_type_name(parser)?;
                PTS::Typeof(ty)
            } else {
                let expr = parse_expression(parser, BindingPower::MIN)?;
                PTS::TypeofExpr(expr)
            };
            parser.expect(TK::RightParen)?;
            Ok(ts)
        }
        TK::Struct | TK::Union => {
            parser.advance();
            let is_union = token.kind == TK::Union;
            parse_record_specifier(parser, is_union)
        }
        TK::Enum => {
            parser.advance();
            parse_enum_specifier(parser)
        }
        TK::Identifier(symbol) => {
            parser.advance();
            Ok(PTS::TypedefName(symbol))
        }
        _ => unreachable!("ICE: Token {:?} should have been validated", token.kind),
    }
}
