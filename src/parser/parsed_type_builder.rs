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
use crate::semantic::TypeQualifiers;
use thin_vec::ThinVec;

use super::Parser;

/// Build a ParsedType from declaration specifiers and an optional declarator
pub(crate) fn build_parsed_type_from_specifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<ParsedDeclSpec>,
    declarator: Option<DeclaratorRef>,
) -> Result<ParsedType, ParseError> {
    let (base_type_ref, qualifiers) = parse_base_type_and_qualifiers(parser, specifiers)?;

    let declarator_ref = if let Some(d) = declarator {
        d
    } else {
        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
    };

    Ok(ParsedType {
        base: base_type_ref,
        declarator: declarator_ref,
        qualifiers,
    })
}

fn merge_parsed_type_specifiers(
    current: ParsedTypeSpec,
    new: ParsedTypeSpec,
    span: crate::ast::SourceSpan,
) -> Result<ParsedTypeSpec, ParseError> {
    use ParsedTypeSpec::*;
    match (current, new) {
        // Redundant same types
        (Long, Long) => Ok(LongLong),
        (Long, Int) => Ok(Long),
        (Int, Long) => Ok(Long),
        (Short, Int) => Ok(Short),
        (Int, Short) => Ok(Short),

        // Signed
        (Signed, Int) => Ok(Int),
        (Int, Signed) => Ok(Int),
        (Signed, Char) => Ok(SignedChar),
        (Char, Signed) => Ok(SignedChar),
        (Signed, Short) => Ok(SignedShort),
        (Short, Signed) => Ok(SignedShort),
        (Signed, Long) => Ok(SignedLong),
        (Long, Signed) => Ok(SignedLong),
        (Signed, LongLong) => Ok(SignedLongLong),
        (LongLong, Signed) => Ok(SignedLongLong),

        // Unsigned
        (Unsigned, Int) => Ok(Unsigned),
        (Int, Unsigned) => Ok(Unsigned),
        (Unsigned, Char) => Ok(UnsignedChar),
        (Char, Unsigned) => Ok(UnsignedChar),
        (Unsigned, Short) => Ok(UnsignedShort),
        (Short, Unsigned) => Ok(UnsignedShort),
        (Unsigned, Long) => Ok(UnsignedLong),
        (Long, Unsigned) => Ok(UnsignedLong),
        (Unsigned, LongLong) => Ok(UnsignedLongLong),
        (LongLong, Unsigned) => Ok(UnsignedLongLong),

        // Complex combinations
        (Long, LongLong) => Ok(LongLong),
        (LongLong, Long) => Ok(LongLong),
        (LongLong, Int) => Ok(LongLong),
        (Int, LongLong) => Ok(LongLong),

        (Signed, Signed) => Ok(Signed),
        (Unsigned, Unsigned) => Ok(Unsigned),

        // Composite + Int (e.g. unsigned long int)
        (UnsignedLong, Int) => Ok(UnsignedLong),
        (Int, UnsignedLong) => Ok(UnsignedLong),
        (SignedLong, Int) => Ok(SignedLong),
        (Int, SignedLong) => Ok(SignedLong),
        (UnsignedLongLong, Int) => Ok(UnsignedLongLong),
        (Int, UnsignedLongLong) => Ok(UnsignedLongLong),
        (SignedLongLong, Int) => Ok(SignedLongLong),
        (Int, SignedLongLong) => Ok(SignedLongLong),
        (UnsignedShort, Int) => Ok(UnsignedShort),
        (Int, UnsignedShort) => Ok(UnsignedShort),
        (SignedShort, Int) => Ok(SignedShort),
        (Int, SignedShort) => Ok(SignedShort),

        // Complex combinations
        (Float, Complex) => Ok(ComplexFloat),
        (Complex, Float) => Ok(ComplexFloat),
        (Double, Complex) => Ok(ComplexDouble),
        (Complex, Double) => Ok(ComplexDouble),
        (LongDouble, Complex) => Ok(ComplexLongDouble),
        (Complex, LongDouble) => Ok(ComplexLongDouble),

        // Mismatch
        _ => Err(ParseError {
            span,
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
                            span: crate::ast::SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    base_type_specifier = Some(match base_type_specifier {
                        Some(current) => {
                            merge_parsed_type_specifiers(current, ts.clone(), crate::ast::SourceSpan::default())?
                        }
                        None => ts.clone(),
                    });
                }
                _ => {
                    if base_type_specifier.is_some() || other_base_type_node.is_some() {
                        return Err(ParseError {
                            span: crate::ast::SourceSpan::default(),
                            kind: ParseErrorKind::UnexpectedToken {
                                expected: "single type specifier",
                                found: TokenKind::Unknown,
                            },
                        });
                    }
                    let parsed_base = parse_type_specifier_to_parsed_base(parser, ts)?;
                    other_base_type_node = Some(parsed_base);
                }
            },
            ParsedDeclSpec::TypeQualifier(q) => {
                qualifiers |= match q {
                    crate::ast::nodes::TypeQualifier::Const => TypeQualifiers::CONST,
                    crate::ast::nodes::TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    crate::ast::nodes::TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    crate::ast::nodes::TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                };
            }
            _ => {}
        }
    }

    let base_type_ref = if let Some(ts) = base_type_specifier {
        parse_type_specifier_to_parsed_base(parser, &ts)?
    } else if let Some(node) = other_base_type_node {
        node
    } else {
        // Default to int if no type specifier found
        // C allows this in some declarations (e.g. static x;), and
        // it's treated as int x;
        parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpec::Int))
    };

    Ok((base_type_ref, qualifiers))
}

/// Convert a TypeSpec to a ParsedBaseTypeNode
fn parse_type_specifier_to_parsed_base(
    parser: &mut Parser,
    ts: &ParsedTypeSpec,
) -> Result<ParsedBaseTypeRef, ParseError> {
    use ParsedTypeSpec::*;
    match ts {
        Void | Char | Short | Int | Long | LongLong | UnsignedLong | UnsignedLongLong | UnsignedShort
        | UnsignedChar | SignedChar | SignedShort | SignedLong | SignedLongLong | Float | Double | LongDouble
        | ComplexFloat | ComplexDouble | ComplexLongDouble | Signed | Unsigned | Bool | Complex | VaList => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ts.clone()))),
        ParsedTypeSpec::Atomic(parsed_type) => {
            // C11 6.7.2.4p3: "The type name in an atomic type specifier shall not designate
            // an array type, a function type, an atomic type, or an incomplete type."
            let decl = parser.ast.parsed_types.get_decl(parsed_type.declarator);
            match decl {
                ParsedDeclarator::Array { .. } => {
                    return Err(ParseError {
                        span: parser.previous_token_span(),
                        kind: ParseErrorKind::Custom {
                            message: "_Atomic(type-name) specifier cannot be used with array type",
                        },
                    });
                }
                ParsedDeclarator::Function { .. } => {
                    return Err(ParseError {
                        span: parser.previous_token_span(),
                        kind: ParseErrorKind::Custom {
                            message: "_Atomic(type-name) specifier cannot be used with function type",
                        },
                    });
                }
                _ => {}
            }

            let base = parser.ast.parsed_types.get_base_type(parsed_type.base);
            if let ParsedBaseTypeNode::Builtin(ParsedTypeSpec::Atomic(_)) = base {
                return Err(ParseError {
                    span: parser.previous_token_span(),
                    kind: ParseErrorKind::Custom {
                        message: "_Atomic(type-name) specifier cannot be used with atomic type",
                    },
                });
            }

            Ok(parser
                .ast
                .parsed_types
                .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpec::Atomic(*parsed_type))))
        }
        ParsedTypeSpec::Record(is_union, tag, definition) => {
            let members = if let Some(def_data) = definition {
                if let Some(member_node_refs) = &def_data.members {
                    let mut parsed_members = Vec::new();
                    for &node_ref in member_node_refs {
                        let node_kind = parser.ast.get_node(node_ref).kind.clone();
                        if let ParsedNodeKind::Declaration(decl) = &node_kind {
                            // Parse each member declaration
                            for init_decl in &decl.init_declarators {
                                if let Some(member_name) = super::declarator::get_declarator_name(
                                    &parser.ast.parsed_types,
                                    init_decl.declarator,
                                ) {
                                    let member_parsed_type = build_parsed_type_from_specifiers(
                                        parser,
                                        &decl.specifiers,
                                        Some(init_decl.declarator),
                                    )?;

                                    // Extract alignment from specifiers
                                    let mut alignment = None;
                                    for spec in &decl.specifiers {
                                        if let ParsedDeclSpec::AlignmentSpec(align_spec) = spec {
                                            match align_spec {
                                                ParsedAlignmentSpec::Expr(expr_ref) => {
                                                    if let ParsedNodeKind::Literal(Literal::Int { val, .. }) =
                                                        parser.ast.get_node(*expr_ref).kind
                                                    {
                                                        alignment = Some(val as u32);
                                                    }
                                                }
                                                ParsedAlignmentSpec::Type(_) => {
                                                    // Handling type alignment in parser is hard, skip for now or resolve during lowering
                                                }
                                            }
                                        }
                                    }

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
                    Some(parser.ast.parsed_types.alloc_struct_members(parsed_members))
                } else {
                    None
                }
            } else {
                None
            };

            Ok(parser.ast.parsed_types.alloc_base_type(ParsedBaseTypeNode::Record {
                tag: *tag,
                members,
                is_union: *is_union,
            }))
        }
        ParsedTypeSpec::Enum(tag, enumerators) => {
            let parsed_enumerators = if let Some(enum_node_refs) = enumerators {
                let mut parsed_enums = Vec::new();
                for &enum_ref in enum_node_refs {
                    let enum_node = parser.ast.get_node(enum_ref);
                    if let ParsedNodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
                        parsed_enums.push(ParsedEnumConstant {
                            name: *name,
                            value: value_expr_ref.as_ref().and_then(|expr_ref| {
                                // Try to evaluate constant expression
                                if let ParsedNodeKind::Literal(Literal::Int { val, .. }) =
                                    parser.ast.get_node(*expr_ref).kind
                                {
                                    Some(val)
                                } else {
                                    None
                                }
                            }),
                            span: enum_node.span,
                        });
                    }
                }
                Some(parser.ast.parsed_types.alloc_enum_constants(parsed_enums))
            } else {
                None
            };

            Ok(parser.ast.parsed_types.alloc_base_type(ParsedBaseTypeNode::Enum {
                tag: *tag,
                enumerators: parsed_enumerators,
            }))
        }
        TypedefName(name) => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Typedef(*name))),
        ParsedTypeSpec::Typeof(ty) => Ok(parser.ast.parsed_types.alloc_base_type(ParsedBaseTypeNode::Typeof(*ty))),
        ParsedTypeSpec::TypeofExpr(expr) => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::TypeofExpr(*expr))),
    }
}

/// Parse a type name and return ParsedType (for casts, sizeof, etc.)
pub(crate) fn parse_parsed_type_name(parser: &mut Parser) -> Result<ParsedType, ParseError> {
    // Parse declaration specifiers
    let specifiers = super::declaration_core::parse_declaration_specifiers(parser)?;

    // Parse abstract declarator (optional)
    let declarator = if parser.is_abstract_declarator_start() {
        Some(super::declarator::parse_abstract_declarator(parser)?)
    } else {
        None
    };

    // Build the ParsedType from specifiers and declarator
    build_parsed_type_from_specifiers(parser, &specifiers, declarator)
}
