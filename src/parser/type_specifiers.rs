//! Type specifier parsing module
//!
//! This module handles parsing of C type specifiers including basic types,
//! typedef names, struct/union/enum specifiers, and atomic types.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::parser::enum_parsing::parse_enum_spec;
use crate::parser::expressions::parse_expression;
use crate::parser::struct_parsing::parse_record_spec;
use crate::parser::type_builder::parse_type_name;
use crate::parser::{BindingPower, TokenKind};

use super::Parser;

/// Parse type specifier
pub(super) fn parse_type_spec(parser: &mut Parser) -> Result<TypeSpec, ParseError> {
    use TokenKind as TK;
    use TypeSpec as TS;

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
                TK::Void => TS::Void,
                TK::Char => TS::Char,
                TK::Short => TS::Short,
                TK::Int => TS::Int,
                TK::Float => TS::Float,
                TK::Double => TS::Double,
                TK::Signed => TS::Signed,
                TK::Unsigned => TS::Unsigned,
                TK::Bool => TS::Bool,
                TK::Complex => TS::Complex,
                TK::BuiltinVaList => TS::VaList,
                TK::AutoType => TS::AutoType,
                _ => unreachable!(),
            })
        }
        TK::Long => {
            parser.advance();
            match parser.current_token_kind() {
                Some(TK::Long) => {
                    parser.advance();
                    Ok(TS::LongLong)
                }
                Some(TK::Double) => {
                    parser.advance();
                    Ok(TS::LongDouble)
                }
                _ => Ok(TS::Long),
            }
        }
        TK::Typeof => {
            parser.advance();
            parser.expect(TK::LeftParen)?;
            let is_type = parser.is_type_name_start();
            let ts = if is_type {
                let ty = parse_type_name(parser)?;
                TS::Typeof(ty)
            } else {
                let expr = parse_expression(parser, BindingPower::MIN)?;
                TS::TypeofExpr(expr)
            };
            parser.expect(TK::RightParen)?;
            Ok(ts)
        }
        TK::TypeofUnqual => {
            parser.advance();
            parser.expect(TK::LeftParen)?;
            let is_type = parser.is_type_name_start();
            let ts = if is_type {
                let ty = parse_type_name(parser)?;
                TS::TypeofUnqual(ty)
            } else {
                let expr = parse_expression(parser, BindingPower::MIN)?;
                TS::TypeofUnqualExpr(expr)
            };
            parser.expect(TK::RightParen)?;
            Ok(ts)
        }
        TK::Struct | TK::Union => {
            parser.advance();
            let is_union = token.kind == TK::Union;
            parse_record_spec(parser, is_union)
        }
        TK::Enum => {
            parser.advance();
            parse_enum_spec(parser)
        }
        TK::Identifier(symbol) => {
            parser.advance();
            Ok(TS::TypedefName(symbol))
        }
        _ => unreachable!("ICE: Token {:?} should have been validated", token.kind),
    }
}
