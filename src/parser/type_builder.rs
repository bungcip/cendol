//! PType builder functions for the parser phase.
//!
//! This module provides helper functions to build Parsed Type objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (PType).

use crate::ast::*;
use crate::parser::declarations::parse_decl_specs;
use crate::parser::declarator::{is_abstract_declarator_start, parse_abstract_declarator};
use crate::parser::{ParseDiag, ParseError, TokenKind};
use crate::semantic::TypeQuals;
use thin_vec::ThinVec;

use super::Parser;

/// Build a ParsedType from declaration specifiers and an optional declarator
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
fn parse_base_type(parser: &mut Parser, ts: TypeSpec) -> Result<crate::ast::parsed_types::PTypeSpecRef, ParseDiag> {
    use TypeSpec::*;
    if let Atomic(parsed_type) = &ts {
        // C11 6.7.2.4p3: "The type name in an atomic type specifier shall not designate
        // an array type, a function type, an atomic type, or an incomplete type."
        let decl = parser.ast.parsed_types.get_decl(parsed_type.declarator);
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

        let base = parser.ast.parsed_types.get_type_spec(parsed_type.base);
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
