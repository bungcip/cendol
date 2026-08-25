//! PType builder functions for the parser phase.
//!
//! This module provides helper functions to build Parsed Type objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (PType).

use crate::ast::*;
use crate::parser::declarations::{parse_decl_specs, parse_enum_spec, parse_record_spec};
use crate::parser::declarator::{is_abstract_declarator_start, parse_abstract_declarator};

use crate::parser::expressions::parse_expression;

use crate::parser::{BindingPower, ParseDiag, ParseError, TokenKind};
use crate::semantic::TypeQuals;

use thin_vec::ThinVec;

use super::Parser;

/// Build a PType from declaration specifiers and an optional declarator
pub(crate) fn build_type(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpec>,
    declarator: Option<DeclaratorRef>,
) -> Result<PType, ParseDiag> {
    let mut quals = TypeQuals::empty();
    let mut first_ts: Option<&TypeSpec> = None;
    let mut merged_ts: Option<TypeSpec> = None;

    let mut declarator = declarator.unwrap_or_else(|| parser.alloc_decl(PDeclarator::Identifier(None)));

    for spec in specifiers.iter().rev() {
        match spec {
            DeclSpec::TypeSpec(ts) => {
                if let Some(merged) = &mut merged_ts {
                    *merged = merge_type_specs(ts, merged)?;
                } else if let Some(first) = first_ts {
                    merged_ts = Some(merge_type_specs(ts, first)?);
                    first_ts = None;
                } else {
                    first_ts = Some(ts);
                }
            }
            DeclSpec::TypeQualifier(q) => {
                quals |= TypeQuals::from_type_qualifier(*q);
            }
            DeclSpec::AlignmentSpec(..)
            | DeclSpec::AttributePacked
            | DeclSpec::AttributeTransparentUnion
            | DeclSpec::AttributeCleanup(_)
            | DeclSpec::AttributeAsm(_)
            | DeclSpec::AttributeAlias(_)
            | DeclSpec::AttributeVisibility(_) => {
                declarator = parser.alloc_decl(PDeclarator::Attribute {
                    inner: declarator,
                    spec: spec.clone(),
                });
            }
            _ => {}
        }
    }

    let base_type = if let Some(ts) = merged_ts {
        parse_base_type(parser, ts)?
    } else if let Some(ts) = first_ts {
        parse_base_type(parser, ts.clone())?
    } else {
        parser.alloc_type_spec(TypeSpec::Int)
    };

    Ok(PType {
        base: base_type,
        declarator,
        quals,
    })
}

fn merge_type_specs(current: &TypeSpec, new: &TypeSpec) -> Result<TypeSpec, ParseDiag> {
    use TypeSpec::*;
    match (current, new) {
        // Redundant same types
        (Long, Long) => Ok(LongLong),
        (Long, Int) | (Int, Long) => Ok(Long),
        (Short, Int) | (Int, Short) => Ok(Short),

        // Signed
        (Signed, Int) | (Int, Signed) => Ok(Int),
        (Signed, Char) | (Char, Signed) => Ok(SignedChar),
        (Signed, Short) | (Short, Signed) => Ok(SignedShort),
        (Signed, Long) | (Long, Signed) => Ok(SignedLong),
        (Signed, LongLong) | (LongLong, Signed) => Ok(SignedLongLong),

        // Unsigned
        (Unsigned, Int) | (Int, Unsigned) => Ok(Unsigned),
        (Unsigned, Char) | (Char, Unsigned) => Ok(UnsignedChar),
        (Unsigned, Short) | (Short, Unsigned) => Ok(UnsignedShort),
        (Unsigned, Long) | (Long, Unsigned) => Ok(UnsignedLong),
        (Unsigned, LongLong) | (LongLong, Unsigned) => Ok(UnsignedLongLong),

        // Complex combinations
        (Long, LongLong) | (LongLong, Long) | (LongLong, Int) | (Int, LongLong) => Ok(LongLong),

        (Signed, Signed) => Ok(Signed),
        (Unsigned, Unsigned) => Ok(Unsigned),

        // Composite + Int (e.g. unsigned long int)
        (UnsignedLong, Int) | (Int, UnsignedLong) => Ok(UnsignedLong),
        (SignedLong, Int) | (Int, SignedLong) => Ok(SignedLong),
        (UnsignedLongLong, Int) | (Int, UnsignedLongLong) => Ok(UnsignedLongLong),
        (SignedLongLong, Int) | (Int, SignedLongLong) => Ok(SignedLongLong),
        (UnsignedShort, Int) | (Int, UnsignedShort) => Ok(UnsignedShort),
        (SignedShort, Int) | (Int, SignedShort) => Ok(SignedShort),

        // Complex combinations
        (Float, Complex) | (Complex, Float) => Ok(ComplexFloat),
        (Double, Complex) | (Complex, Double) => Ok(ComplexDouble),
        (LongDouble, Complex) | (Complex, LongDouble) => Ok(ComplexLongDouble),

        (AutoType, AutoType) => Ok(AutoType),

        // Mismatch
        _ => Err(ParseDiag {
            span: SourceSpan::default(),
            kind: ParseError::UnexpectedToken {
                expected: "compatible type specifier",
                found: TokenKind::Unknown,
            },
        }),
    }
}

/// Convert a TypeSpec to a PTypeSpecRef (verifying constraints)
fn parse_base_type(parser: &mut Parser, ts: TypeSpec) -> Result<TypeSpecRef, ParseDiag> {
    use TypeSpec::*;
    if let Atomic(ptype) = &ts {
        // C11 6.7.2.4p3: "The type name in an atomic type specifier shall not designate
        // an array type, a function type, an atomic type, or an incomplete type."
        let decl = parser.ast.arena.get_decl(ptype.declarator);
        match decl {
            PDeclarator::Array { .. } => {
                return Err(ParseDiag {
                    span: parser.previous_token_span(),
                    kind: ParseError::InvalidAtomicSpec("array"),
                });
            }
            PDeclarator::Function { .. } => {
                return Err(ParseDiag {
                    span: parser.previous_token_span(),
                    kind: ParseError::InvalidAtomicSpec("function"),
                });
            }
            _ => {}
        }

        let base = parser.ast.arena.get_type_spec(ptype.base);
        if let Atomic(_) = base {
            return Err(ParseDiag {
                span: parser.previous_token_span(),
                kind: ParseError::InvalidAtomicSpec("atomic"),
            });
        }
    }

    Ok(parser.alloc_type_spec(ts))
}

/// Parse a type name and return ParsedType (for casts, sizeof, etc.)
pub(crate) fn parse_type_name(parser: &mut Parser) -> Result<PType, ParseDiag> {
    // Parse declaration specifiers
    let specifiers = parse_decl_specs(parser)?;

    // Parse abstract declarator (optional)
    let declarator = if is_abstract_declarator_start(parser) {
        Some(parse_abstract_declarator(parser, false)?)
    } else {
        None
    };

    // Build the ParsedType from specifiers and declarator
    build_type(parser, &specifiers, declarator)
}

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
