//! ParsedType builder functions for the parser phase.
//!
//! This module provides helper functions to build ParsedType objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (ParsedType).

use crate::ast::literal::Literal;
use crate::ast::*;
use crate::diagnostic::{ParseError, ParseErrorKind};
use crate::parser::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::declarator::{get_declarator_name, parse_abstract_declarator};
use crate::semantic::TypeQualifiers;
use thin_vec::ThinVec;

use super::Parser;

/// Build a ParsedType from declaration specifiers and an optional declarator
pub(crate) fn build_type(
    parser: &mut Parser,
    specifiers: &ThinVec<ParsedDeclSpec>,
    declarator: Option<DeclaratorRef>,
) -> Result<ParsedType, ParseError> {
    let (base_type_ref, qualifiers) = parse_base_type_and_qualifiers(parser, specifiers)?;

    let declarator_ref = if let Some(d) = declarator {
        d
    } else {
        parser.alloc_decl(ParsedDeclarator::Identifier(None))
    };

    Ok(ParsedType {
        base: base_type_ref,
        declarator: declarator_ref,
        qualifiers,
    })
}

fn merge_type_specifiers(current: ParsedTypeSpec, new: ParsedTypeSpec) -> Result<ParsedTypeSpec, ParseError> {
    use ParsedTypeSpec::*;
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
    specifiers: &ThinVec<ParsedDeclSpec>,
) -> Result<(ParsedBaseTypeRef, TypeQualifiers), ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    let mut base_type_specifier: Option<ParsedTypeSpec> = None;
    let mut other_base_type_node = None;

    for spec in specifiers {
        match spec {
            ParsedDeclSpec::TypeSpec(ts) => match ts {
                ParsedTypeSpec::Void
                | ParsedTypeSpec::Char
                | ParsedTypeSpec::Short
                | ParsedTypeSpec::Int
                | ParsedTypeSpec::Long
                | ParsedTypeSpec::LongLong
                | ParsedTypeSpec::Float
                | ParsedTypeSpec::Double
                | ParsedTypeSpec::LongDouble
                | ParsedTypeSpec::Signed
                | ParsedTypeSpec::Unsigned
                | ParsedTypeSpec::Bool
                | ParsedTypeSpec::Complex => {
                    if other_base_type_node.is_some() {
                        return Err(ParseError {
                            span: SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    base_type_specifier = Some(match base_type_specifier {
                        Some(curr) => merge_type_specifiers(curr, ts.clone())?,
                        None => ts.clone(),
                    });
                }
                _ => {
                    if base_type_specifier.is_some() || other_base_type_node.is_some() {
                        return Err(ParseError {
                            span: SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    other_base_type_node = Some(parse_base_type(parser, ts)?);
                }
            },
            ParsedDeclSpec::TypeQualifier(q) => {
                qualifiers |= match q {
                    TypeQualifier::Const => TypeQualifiers::CONST,
                    TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                };
            }
            _ => {}
        }
    }

    let base_type_ref = if let Some(ts) = base_type_specifier {
        parse_base_type(parser, &ts)?
    } else if let Some(node) = other_base_type_node {
        node
    } else {
        parser.alloc_base_type(ParsedBaseType::Builtin(ParsedTypeSpec::Int))
    };

    Ok((base_type_ref, qualifiers))
}

/// Convert a TypeSpec to a ParsedBaseType
fn parse_base_type(parser: &mut Parser, ts: &ParsedTypeSpec) -> Result<ParsedBaseTypeRef, ParseError> {
    use ParsedTypeSpec::*;
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
        Record(is_union, tag, definition) => {
            let members = if let Some(def_data) = definition {
                def_data
                    .members
                    .as_ref()
                    .map(|m| parse_record_members(parser, m))
                    .transpose()?
            } else {
                None
            };

            Ok(parser.alloc_base_type(ParsedBaseType::Record {
                tag: *tag,
                members,
                is_union: *is_union,
            }))
        }
        Enum(tag, enumerators) => {
            let enumerators = enumerators
                .as_ref()
                .map(|e| parse_enum_constants(parser, e))
                .transpose()?;

            Ok(parser.alloc_base_type(ParsedBaseType::Enum { tag: *tag, enumerators }))
        }
        TypedefName(name) => Ok(parser.alloc_base_type(ParsedBaseType::Typedef(*name))),
        AutoType => Ok(parser.alloc_base_type(ParsedBaseType::Builtin(AutoType))),
        Typeof(ty) => Ok(parser.alloc_base_type(ParsedBaseType::Typeof(*ty))),
        TypeofExpr(expr) => Ok(parser.alloc_base_type(ParsedBaseType::TypeofExpr(*expr))),
    }
}

/// Parse a type name and return ParsedType (for casts, sizeof, etc.)
pub(crate) fn parse_type_name(parser: &mut Parser) -> Result<ParsedType, ParseError> {
    // Parse declaration specifiers
    let specifiers = parse_declaration_specifiers(parser)?;

    // Parse abstract declarator (optional)
    let declarator = if parser.is_abstract_declarator_start() {
        Some(parse_abstract_declarator(parser)?)
    } else {
        None
    };

    // Build the ParsedType from specifiers and declarator
    build_type(parser, &specifiers, declarator)
}

fn parse_record_members(
    parser: &mut Parser,
    member_node_refs: &[ParsedNodeRef],
) -> Result<ParsedStructMemberRange, ParseError> {
    let mut parsed_members = Vec::new();
    for &node_ref in member_node_refs {
        let node_kind = parser.ast.get_node(node_ref).kind.clone();
        if let ParsedNodeKind::Declaration(decl) = &node_kind {
            for init_decl in &decl.init_declarators {
                if let Some(member_name) = get_declarator_name(&parser.ast.parsed_types, init_decl.declarator) {
                    let member_parsed_type = build_type(parser, &decl.specifiers, Some(init_decl.declarator))?;
                    let alignment = extract_alignment(&decl.specifiers, parser);

                    parsed_members.push(ParsedStructMember {
                        name: Some(member_name),
                        ty: member_parsed_type,
                        bit_field_size: None,
                        alignment,
                        span: init_decl.span,
                    });
                }
            }
        }
    }
    Ok(parser.alloc_struct_members(parsed_members))
}

fn extract_alignment(specifiers: &[ParsedDeclSpec], parser: &Parser) -> Option<u32> {
    for spec in specifiers {
        if let ParsedDeclSpec::AlignmentSpec(align_spec) = spec
            && let ParsedAlignmentSpec::Expr(expr_ref) = align_spec
            && let ParsedNodeKind::Literal(Literal::Int { val, .. }) = parser.ast.get_node(*expr_ref).kind
        {
            return Some(val as u32);
        }
    }
    None
}

fn parse_enum_constants(parser: &mut Parser, enum_node_refs: &[ParsedNodeRef]) -> Result<ParsedEnumRange, ParseError> {
    let mut parsed_enums = Vec::new();
    for &enum_ref in enum_node_refs {
        let enum_node = parser.ast.get_node(enum_ref);
        if let ParsedNodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
            parsed_enums.push(ParsedEnumConstant {
                name: *name,
                value: value_expr_ref.as_ref().and_then(|expr_ref| {
                    if let ParsedNodeKind::Literal(Literal::Int { val, .. }) = parser.ast.get_node(*expr_ref).kind {
                        Some(val)
                    } else {
                        None
                    }
                }),
                span: enum_node.span,
            });
        }
    }
    Ok(parser.alloc_enum_constants(parsed_enums))
}
