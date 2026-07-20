//! ParsedType builder functions for the parser phase.
//!
//! This module provides helper functions to build ParsedType objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (ParsedType).

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
    let (base, quals) = parse_base_type_and_quals(parser, specifiers)?;

    let mut declarator = if let Some(d) = declarator {
        d
    } else {
        parser.alloc_decl(PDeclarator::Identifier(None))
    };

    for spec in specifiers.iter().rev() {
        if matches!(
            spec,
            DeclSpec::AlignmentSpec(..)
                | DeclSpec::AttributePacked
                | DeclSpec::AttributeTransparentUnion
                | DeclSpec::AttributeCleanup(_)
                | DeclSpec::AttributeAsm(_)
                | DeclSpec::AttributeAlias(_)
                | DeclSpec::AttributeVisibility(_)
        ) {
            declarator = parser.alloc_decl(PDeclarator::Attribute {
                inner: declarator,
                spec: spec.clone(),
            });
        }
    }

    Ok(PType {
        base,
        declarator,
        quals,
    })
}

fn merge_type_specs(current: TypeSpec, new: TypeSpec) -> Result<TypeSpec, ParseDiag> {
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

/// Parse base type and qualifiers from declaration specifiers
fn parse_base_type_and_quals(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpec>,
) -> Result<(crate::ast::parsed_types::PTypeSpecRef, TypeQuals), ParseDiag> {
    let mut quals = TypeQuals::empty();
    let mut base_type_spec: Option<TypeSpec> = None;
    let mut other_base_type = None;

    for spec in specifiers {
        match spec {
            DeclSpec::TypeSpec(ts) => match ts {
                TypeSpec::Void
                | TypeSpec::Char
                | TypeSpec::Char8
                | TypeSpec::Short
                | TypeSpec::Int
                | TypeSpec::Long
                | TypeSpec::LongLong
                | TypeSpec::Float
                | TypeSpec::Double
                | TypeSpec::LongDouble
                | TypeSpec::Signed
                | TypeSpec::Unsigned
                | TypeSpec::Bool
                | TypeSpec::Complex => {
                    if other_base_type.is_some() {
                        return Err(ParseDiag {
                            span: SourceSpan::default(),
                            kind: ParseError::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    base_type_spec = Some(match base_type_spec {
                        Some(curr) => merge_type_specs(curr, ts.clone())?,
                        None => ts.clone(),
                    });
                }
                _ => {
                    if base_type_spec.is_some() || other_base_type.is_some() {
                        return Err(ParseDiag {
                            span: SourceSpan::default(),
                            kind: ParseError::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    other_base_type = Some(parse_base_type(parser, ts)?);
                }
            },
            DeclSpec::TypeQualifier(q) => {
                quals |= TypeQuals::from_type_qualifier(*q);
            }
            _ => {}
        }
    }

    let base_type = if let Some(ts) = base_type_spec {
        parse_base_type(parser, &ts)?
    } else if let Some(node) = other_base_type {
        node
    } else {
        parser.alloc_type_spec(TypeSpec::Int)
    };

    Ok((base_type, quals))
}

/// Convert a TypeSpec to a ParsedTypeSpecRef (verifying constraints)
fn parse_base_type(parser: &mut Parser, ts: &TypeSpec) -> Result<crate::ast::parsed_types::PTypeSpecRef, ParseDiag> {
    use TypeSpec::*;
    if let Atomic(parsed_type) = ts {
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

    Ok(parser.alloc_type_spec(ts.clone()))
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
