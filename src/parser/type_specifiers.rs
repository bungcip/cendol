//! Type specifier parsing module
//!
//! This module handles parsing of C type specifiers including basic types,
//! typedef names, struct/union/enum specifiers, and atomic types.

use crate::ast::*;
use crate::parser::enum_parsing::parse_enum_spec;
use crate::parser::expressions::parse_expression;
use crate::parser::struct_parsing::parse_record_spec;
use crate::parser::type_builder::parse_type_name;
use crate::parser::{BindingPower, ParseDiag, TokenKind};

use super::Parser;

/// Parse type specifier
pub(super) fn parse_type_spec(parser: &mut Parser) -> Result<TypeSpec, ParseDiag> {
    use TokenKind as TK;
    use TypeSpec as TS;

    let token = parser.current_token()?;
    parser.advance();

    match token.kind {
        TK::Void => Ok(TS::Void),
        TK::Char => Ok(TS::Char),
        TK::Char8 => Ok(TS::Char8),
        TK::Short => Ok(TS::Short),
        TK::Int => Ok(TS::Int),
        TK::Float => Ok(TS::Float),
        TK::Double => Ok(TS::Double),
        TK::Signed => Ok(TS::Signed),
        TK::Unsigned => Ok(TS::Unsigned),
        TK::Bool => Ok(TS::Bool),
        TK::Complex => Ok(TS::Complex),
        TK::BuiltinVaList => Ok(TS::VaList),
        TK::AutoType => Ok(TS::AutoType),

        TK::Long => match parser.current_token_kind() {
            Some(TK::Long) => {
                parser.advance();
                Ok(TS::LongLong)
            }
            Some(TK::Double) => {
                parser.advance();
                Ok(TS::LongDouble)
            }
            _ => Ok(TS::Long),
        },

        TK::Typeof | TK::TypeofUnqual => {
            let is_unqual = token.kind == TK::TypeofUnqual;
            parser.expect(TK::LeftParen)?;

            let ts = if parser.is_type_name_start() {
                let ty = parse_type_name(parser)?;
                if is_unqual {
                    TS::TypeofUnqual(ty)
                } else {
                    TS::Typeof(ty)
                }
            } else {
                let expr = parse_expression(parser, BindingPower::MIN)?;
                if is_unqual {
                    TS::TypeofUnqualExpr(expr)
                } else {
                    TS::TypeofExpr(expr)
                }
            };

            parser.expect(TK::RightParen)?;
            Ok(ts)
        }

        TK::Struct | TK::Union => {
            let is_union = token.kind == TK::Union;
            parse_record_spec(parser, is_union)
        }

        TK::Enum => parse_enum_spec(parser),

        TK::Identifier(symbol) => Ok(TS::TypedefName(symbol)),

        _ => unreachable!("ICE: Token {:?} should have been validated", token.kind),
    }
}
