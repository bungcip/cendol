//! ParsedType builder functions for the parser phase.
//!
//! This module provides helper functions to build ParsedType objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (ParsedType).

use crate::ast::literal::LitVal;
use crate::ast::*;
use crate::parser::declarations::parse_decl_specs;
use crate::parser::declarator::{get_declarator_name, is_abstract_declarator_start, parse_abstract_declarator};
use crate::parser::{ParseError, ParseErrorKind, TokenKind};
use crate::semantic::TypeQualifiers;
use thin_vec::ThinVec;

use super::Parser;

/// Build a ParsedType from declaration specifiers and an optional declarator
pub(crate) fn build_type(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpec>,
    declarator: Option<DeclaratorRef>,
) -> Result<ParsedType, ParseError> {
    let (base, qualifiers) = parse_base_type_and_qualifiers(parser, specifiers)?;

    let declarator = if let Some(d) = declarator {
        d
    } else {
        parser.alloc_decl(ParsedDeclarator::Identifier(None))
    };

    Ok(ParsedType {
        base,
        declarator,
        qualifiers,
    })
}

fn merge_type_specs(current: TypeSpec, new: TypeSpec) -> Result<TypeSpec, ParseError> {
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
        _ => Err(ParseError {
            span: SourceSpan::default(),
            kind: ParseErrorKind::UnexpectedToken {
                expected: "compatible type specifier",
                found: TokenKind::Unknown,
            },
        }),
    }
}

/// Parse base type and qualifiers from declaration specifiers
fn parse_base_type_and_qualifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpec>,
) -> Result<(ParsedBaseTypeRef, TypeQualifiers), ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    let mut base_type_spec: Option<TypeSpec> = None;
    let mut other_base_type = None;

    for spec in specifiers {
        match spec {
            DeclSpec::TypeSpec(ts) => match ts {
                TypeSpec::Void
                | TypeSpec::Char
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
                        return Err(ParseError {
                            span: SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
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
                        return Err(ParseError {
                            span: SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    other_base_type = Some(parse_base_type(parser, ts)?);
                }
            },
            DeclSpec::TypeQualifier(q) => {
                qualifiers |= TypeQualifiers::from_type_qualifier(*q);
            }
            _ => {}
        }
    }

    let base_type = if let Some(ts) = base_type_spec {
        parse_base_type(parser, &ts)?
    } else if let Some(node) = other_base_type {
        node
    } else {
        parser.alloc_base_type(ParsedBaseType::Builtin(TypeSpec::Int))
    };

    Ok((base_type, qualifiers))
}

/// Convert a TypeSpec to a ParsedBaseType
fn parse_base_type(parser: &mut Parser, ts: &TypeSpec) -> Result<ParsedBaseTypeRef, ParseError> {
    use TypeSpec::*;
    match ts {
        Void | Char | Short | Int | Long | LongLong | UnsignedLong | UnsignedLongLong | UnsignedShort
        | UnsignedChar | SignedChar | SignedShort | SignedLong | SignedLongLong | Float | Double | LongDouble
        | ComplexFloat | ComplexDouble | ComplexLongDouble | Signed | Unsigned | Bool | Complex | VaList => {
            Ok(parser.alloc_base_type(ParsedBaseType::Builtin(ts.clone())))
        }
        Atomic(parsed_type) => {
            // C11 6.7.2.4p3: "The type name in an atomic type specifier shall not designate
            // an array type, a function type, an atomic type, or an incomplete type."
            let decl = parser.ast.parsed_types.get_decl(parsed_type.declarator);
            match decl {
                ParsedDeclarator::Array { .. } => {
                    return Err(ParseError {
                        span: parser.previous_token_span(),
                        kind: ParseErrorKind::InvalidAtomicSpec("array"),
                    });
                }
                ParsedDeclarator::Function { .. } => {
                    return Err(ParseError {
                        span: parser.previous_token_span(),
                        kind: ParseErrorKind::InvalidAtomicSpec("function"),
                    });
                }
                _ => {}
            }

            let base = parser.ast.parsed_types.get_base_type(parsed_type.base);
            if let ParsedBaseType::Builtin(Atomic(_)) = base {
                return Err(ParseError {
                    span: parser.previous_token_span(),
                    kind: ParseErrorKind::InvalidAtomicSpec("atomic"),
                });
            }

            Ok(parser.alloc_base_type(ParsedBaseType::Builtin(Atomic(*parsed_type))))
        }
        Record(is_union, tag, definition, _) => {
            let members = if let Some(decls) = definition {
                Some(parse_record_members(parser, decls)?)
            } else {
                None
            };

            Ok(parser.alloc_base_type(ParsedBaseType::Record {
                tag: *tag,
                members,
                is_union: *is_union,
            }))
        }
        Enum(tag, enumerators, underlying_type) => {
            let enumerators = enumerators
                .as_ref()
                .map(|e| parse_enum_constants(parser, e))
                .transpose()?;

            Ok(parser.alloc_base_type(ParsedBaseType::Enum {
                tag: *tag,
                enumerators,
                underlying_type: *underlying_type,
            }))
        }
        TypedefName(name) => Ok(parser.alloc_base_type(ParsedBaseType::Typedef(*name))),
        AutoType => Ok(parser.alloc_base_type(ParsedBaseType::Builtin(AutoType))),
        Typeof(ty) => Ok(parser.alloc_base_type(ParsedBaseType::Typeof(*ty))),
        TypeofExpr(expr) => Ok(parser.alloc_base_type(ParsedBaseType::TypeofExpr(*expr))),
        TypeofUnqual(ty) => Ok(parser.alloc_base_type(ParsedBaseType::TypeofUnqual(*ty))),
        TypeofUnqualExpr(expr) => Ok(parser.alloc_base_type(ParsedBaseType::TypeofUnqualExpr(*expr))),
    }
}

/// Parse a type name and return ParsedType (for casts, sizeof, etc.)
pub(crate) fn parse_type_name(parser: &mut Parser) -> Result<ParsedType, ParseError> {
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

fn parse_record_members(
    parser: &mut Parser,
    member_nodes: &[ParsedNodeRef],
) -> Result<ParsedStructMemberRange, ParseError> {
    let mut parsed_members = Vec::new();
    for &node in member_nodes {
        let node_kind = parser.ast.get_node(node).kind.clone();
        if let ParsedNodeKind::Declaration(decl) = &node_kind {
            for init_decl in &decl.init_declarators {
                if let Some(member_name) = get_declarator_name(&parser.ast.parsed_types, init_decl.declarator) {
                    let member_parsed_type = build_type(parser, &decl.specifiers, Some(init_decl.declarator))?;
                    let alignment = extract_alignment(&decl.specifiers, parser);
                    let is_packed = extract_is_packed(&decl.specifiers);

                    parsed_members.push(ParsedStructMember {
                        name: Some(member_name),
                        ty: member_parsed_type,
                        bit_field_size: None,
                        alignment,
                        is_packed,
                        span: init_decl.span,
                    });
                }
            }
        }
    }
    Ok(parser.alloc_struct_members(parsed_members))
}

fn extract_alignment(specifiers: &[DeclSpec], parser: &Parser) -> Option<u16> {
    for spec in specifiers {
        if let DeclSpec::AlignmentSpec(align_spec, _) = spec {
            match align_spec {
                ParsedAlignmentSpec::Expr(expr) => {
                    if let ParsedNodeKind::Literal(lit) = parser.ast.get_node(*expr).kind
                        && let LitVal::Int { value, .. } = lit.get_val()
                    {
                        return Some(value as u16);
                    }
                }
                ParsedAlignmentSpec::Type(_) => {
                    // Type-based alignment is harder to extract during parsing without a registry.
                    // For now, we skip it here. It will be handled during lowering.
                }
            }
        }
    }
    None
}

fn extract_is_packed(specifiers: &[DeclSpec]) -> bool {
    specifiers.iter().any(|s| matches!(s, DeclSpec::AttributePacked))
}

fn parse_enum_constants(parser: &mut Parser, enum_nodes: &[ParsedNodeRef]) -> Result<ParsedEnumRange, ParseError> {
    let mut parsed_enums = Vec::new();
    for &enum_node in enum_nodes {
        let enum_node = parser.ast.get_node(enum_node);
        if let ParsedNodeKind::EnumConstant(name, value_expr) = &enum_node.kind {
            parsed_enums.push(ParsedEnumConstant {
                name: *name,
                value: value_expr.as_ref().and_then(|expr| {
                    if let ParsedNodeKind::Literal(lit) = parser.ast.get_node(*expr).kind
                        && let LitVal::Int { value, .. } = lit.get_val()
                    {
                        return Some(value);
                    }
                    None
                }),
                span: enum_node.span,
            });
        }
    }
    Ok(parser.alloc_enum_constants(parsed_enums))
}
