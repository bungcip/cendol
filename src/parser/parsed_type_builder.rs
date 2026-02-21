//! ParsedType builder functions for the parser phase.
//!
//! This module provides helper functions to build ParsedType objects
//! from declaration specifiers and declarators during the parsing phase.
//! These functions ensure that no semantic types (TypeRef) are created
//! during parsing, only syntactic types (ParsedType).

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::semantic::TypeQualifiers;
use thin_vec::ThinVec;

use super::Parser;

/// Build a ParsedType from declaration specifiers and an optional declarator
pub(crate) fn build_parsed_type_from_specifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<ParsedDeclSpecifier>,
    declarator: Option<&ParsedDeclarator>,
) -> Result<ParsedType, ParseError> {
    let (base_type_ref, qualifiers) = parse_base_type_and_qualifiers(parser, specifiers)?;

    let declarator_ref = if let Some(d) = declarator {
        build_parsed_declarator(parser, d)?
    } else {
        parser
            .ast
            .parsed_types
            .alloc_decl(ParsedDeclaratorNode::Identifier { name: None })
    };

    Ok(ParsedType {
        base: base_type_ref,
        declarator: declarator_ref,
        qualifiers,
    })
}

fn merge_parsed_type_specifiers(
    current: ParsedTypeSpecifier,
    new: ParsedTypeSpecifier,
    span: crate::ast::SourceSpan,
) -> Result<ParsedTypeSpecifier, ParseError> {
    use ParsedTypeSpecifier::*;
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
        (a, _) => Err(ParseError::UnexpectedToken {
            expected_tokens: format!("compatible type specifier for {:?}", a),
            found: crate::parser::TokenKind::Unknown,
            span,
        }),
    }
}

/// Parse base type and qualifiers from declaration specifiers
fn parse_base_type_and_qualifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<ParsedDeclSpecifier>,
) -> Result<(ParsedBaseTypeRef, TypeQualifiers), ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    let mut base_type_specifier: Option<ParsedTypeSpecifier> = None;
    let mut other_base_type_node = None;

    for spec in specifiers {
        match spec {
            ParsedDeclSpecifier::TypeSpecifier(ts) => {
                match ts {
                    // Collect mergeable basic types
                    ParsedTypeSpecifier::Void
                    | ParsedTypeSpecifier::Char
                    | ParsedTypeSpecifier::Short
                    | ParsedTypeSpecifier::Int
                    | ParsedTypeSpecifier::Long
                    | ParsedTypeSpecifier::LongLong
                    | ParsedTypeSpecifier::Float
                    | ParsedTypeSpecifier::Double
                    | ParsedTypeSpecifier::LongDouble
                    | ParsedTypeSpecifier::Signed
                    | ParsedTypeSpecifier::Unsigned
                    | ParsedTypeSpecifier::Bool
                    | ParsedTypeSpecifier::Complex => {
                        if other_base_type_node.is_some() {
                            return Err(ParseError::UnexpectedToken {
                                expected_tokens: "single type specifier".to_string(),
                                found: crate::parser::TokenKind::Unknown,
                                span: crate::ast::SourceSpan::default(),
                            });
                        }
                        if let Some(current) = base_type_specifier {
                            // Merge
                            // We don't have span for specifiers in ThinVec directly?
                            // We can use parser.current_span() but that's wrong.
                            // ParsedDeclSpecifier doesn't store span.
                            // We will assume dummy span for now or fix this later.
                            base_type_specifier = Some(merge_parsed_type_specifiers(
                                current,
                                ts.clone(),
                                crate::ast::SourceSpan::default(),
                            )?);
                        } else {
                            base_type_specifier = Some(ts.clone());
                        }
                    }
                    _ => {
                        // Non-mergeable types (struct, enum, typedef, atomic)
                        // Should error if we already have a type
                        if base_type_specifier.is_some() || other_base_type_node.is_some() {
                            // Error: multiple types
                            // Since we don't have easy error here, we might just overwrite or error?
                            // Let's error.
                            return Err(ParseError::UnexpectedToken {
                                expected_tokens: "single type specifier".to_string(),
                                found: crate::parser::TokenKind::Unknown,
                                span: crate::ast::SourceSpan::default(),
                            });
                        }
                        let parsed_base = parse_type_specifier_to_parsed_base(parser, ts)?;
                        other_base_type_node = Some(parsed_base);
                    }
                }
            }
            ParsedDeclSpecifier::TypeQualifier(q) => {
                let qualifier = match q {
                    crate::ast::nodes::TypeQualifier::Const => TypeQualifiers::CONST,
                    crate::ast::nodes::TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    crate::ast::nodes::TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    crate::ast::nodes::TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                };
                qualifiers |= qualifier;
            }
            _ => {
                // Other specifiers (storage class, function specifiers, etc.)
                // are handled elsewhere and don't affect the base type
            }
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
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Int))
    };

    Ok((base_type_ref, qualifiers))
}

/// Convert a TypeSpecifier to a ParsedBaseTypeNode
fn parse_type_specifier_to_parsed_base(
    parser: &mut Parser,
    ts: &ParsedTypeSpecifier,
) -> Result<ParsedBaseTypeRef, ParseError> {
    match ts {
        ParsedTypeSpecifier::Void => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Void))),
        ParsedTypeSpecifier::Char => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Char))),
        ParsedTypeSpecifier::Short => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Short))),
        ParsedTypeSpecifier::Int => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Int))),
        ParsedTypeSpecifier::Long => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Long))),
        ParsedTypeSpecifier::LongLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::LongLong))),

        // New variants
        ParsedTypeSpecifier::UnsignedLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::UnsignedLong))),
        ParsedTypeSpecifier::UnsignedLongLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::UnsignedLongLong))),
        ParsedTypeSpecifier::UnsignedShort => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::UnsignedShort))),
        ParsedTypeSpecifier::UnsignedChar => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::UnsignedChar))),
        ParsedTypeSpecifier::SignedChar => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::SignedChar))),
        ParsedTypeSpecifier::SignedShort => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::SignedShort))),
        ParsedTypeSpecifier::SignedLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::SignedLong))),
        ParsedTypeSpecifier::SignedLongLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::SignedLongLong))),

        ParsedTypeSpecifier::Float => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Float))),
        ParsedTypeSpecifier::Double => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Double))),
        ParsedTypeSpecifier::LongDouble => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::LongDouble))),
        ParsedTypeSpecifier::ComplexFloat => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::ComplexFloat))),
        ParsedTypeSpecifier::ComplexDouble => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::ComplexDouble))),
        ParsedTypeSpecifier::ComplexLongDouble => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::ComplexLongDouble))),
        ParsedTypeSpecifier::Signed => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Signed))),
        ParsedTypeSpecifier::Unsigned => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Unsigned))),
        ParsedTypeSpecifier::Bool => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Bool))),
        ParsedTypeSpecifier::Complex => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Complex))),
        ParsedTypeSpecifier::Atomic(parsed_type) => {
            // C11 6.7.2.4p3: "The type name in an atomic type specifier shall not designate
            // an array type, a function type, an atomic type, or an incomplete type."
            let decl = parser.ast.parsed_types.get_decl(parsed_type.declarator);
            match decl {
                ParsedDeclaratorNode::Array { .. } => {
                    return Err(ParseError::Custom {
                        message: "_Atomic(type-name) specifier cannot be used with array type".to_string(),
                        span: parser.previous_token_span(),
                    });
                }
                ParsedDeclaratorNode::Function { .. } => {
                    return Err(ParseError::Custom {
                        message: "_Atomic(type-name) specifier cannot be used with function type".to_string(),
                        span: parser.previous_token_span(),
                    });
                }
                _ => {}
            }

            let base = parser.ast.parsed_types.get_base_type(parsed_type.base);
            if let ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Atomic(_)) = base {
                return Err(ParseError::Custom {
                    message: "_Atomic(type-name) specifier cannot be used with atomic type".to_string(),
                    span: parser.previous_token_span(),
                });
            }

            Ok(parser
                .ast
                .parsed_types
                .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::Atomic(*parsed_type))))
        }
        ParsedTypeSpecifier::Record(is_union, tag, definition) => {
            let members = if let Some(def_data) = definition {
                if let Some(member_node_refs) = &def_data.members {
                    let mut parsed_members = Vec::new();
                    for &node_ref in member_node_refs {
                        let node_kind = parser.ast.get_node(node_ref).kind.clone();
                        if let ParsedNodeKind::Declaration(decl) = &node_kind {
                            // Parse each member declaration
                            for init_decl in &decl.init_declarators {
                                if let Some(member_name) = super::declarator::get_declarator_name(&init_decl.declarator)
                                {
                                    let member_parsed_type = build_parsed_type_from_specifiers(
                                        parser,
                                        &decl.specifiers,
                                        Some(&init_decl.declarator),
                                    )?;

                                    // Extract alignment from specifiers
                                    let mut alignment = None;
                                    for spec in &decl.specifiers {
                                        if let ParsedDeclSpecifier::AlignmentSpecifier(align_spec) = spec {
                                            match align_spec {
                                                ParsedAlignmentSpecifier::Expr(expr_ref) => {
                                                    if let ParsedNodeKind::Literal(literal::Literal::Int {
                                                        val, ..
                                                    }) = parser.ast.get_node(*expr_ref).kind
                                                    {
                                                        alignment = Some(val as u32);
                                                    }
                                                }
                                                ParsedAlignmentSpecifier::Type(_) => {
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
        ParsedTypeSpecifier::Enum(tag, enumerators) => {
            let parsed_enumerators = if let Some(enum_node_refs) = enumerators {
                let mut parsed_enums = Vec::new();
                for &enum_ref in enum_node_refs {
                    let enum_node = parser.ast.get_node(enum_ref);
                    if let ParsedNodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
                        parsed_enums.push(ParsedEnumConstant {
                            name: *name,
                            value: value_expr_ref.as_ref().and_then(|expr_ref| {
                                // Try to evaluate constant expression
                                if let ParsedNodeKind::Literal(literal::Literal::Int { val, .. }) =
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
        ParsedTypeSpecifier::TypedefName(name) => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Typedef(*name))),
        ParsedTypeSpecifier::VaList => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(ParsedTypeSpecifier::VaList))),
    }
}

/// Build a ParsedDeclaratorNode from a ParsedDeclarator
fn build_parsed_declarator(parser: &mut Parser, declarator: &ParsedDeclarator) -> Result<ParsedDeclRef, ParseError> {
    match declarator {
        ParsedDeclarator::Identifier(name, _qualifiers) => {
            // Simple identifier
            // Note: qualifiers are part of specifiers or pointers, not directly on identifiers
            // in the parser's logic for identifiers.
            Ok(parser
                .ast
                .parsed_types
                .alloc_decl(ParsedDeclaratorNode::Identifier { name: Some(*name) }))
        }
        ParsedDeclarator::Pointer(ptr_qualifiers, inner_decl) => {
            let inner_ref = if let Some(inner) = inner_decl {
                build_parsed_declarator(parser, inner)?
            } else {
                parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclaratorNode::Identifier { name: None })
            };

            Ok(parser.ast.parsed_types.alloc_decl(ParsedDeclaratorNode::Pointer {
                qualifiers: *ptr_qualifiers,
                inner: inner_ref,
            }))
        }
        ParsedDeclarator::Array(inner, size) => {
            let inner_ref = build_parsed_declarator(parser, inner)?;

            Ok(parser.ast.parsed_types.alloc_decl(ParsedDeclaratorNode::Array {
                size: size.clone(),
                inner: inner_ref,
            }))
        }
        ParsedDeclarator::Function {
            inner,
            params,
            is_variadic,
        } => {
            let inner_ref = build_parsed_declarator(parser, inner)?;

            // Parse parameters
            let mut parsed_params = Vec::new();
            for param in params {
                let param_parsed_type =
                    build_parsed_type_from_specifiers(parser, &param.specifiers, param.declarator.as_ref())?;

                parsed_params.push(ParsedFunctionParam {
                    name: param
                        .declarator
                        .as_ref()
                        .and_then(super::declarator::get_declarator_name),
                    ty: param_parsed_type,
                    span: param.span,
                });
            }

            let param_range = parser.ast.parsed_types.alloc_params(parsed_params);

            Ok(parser.ast.parsed_types.alloc_decl(ParsedDeclaratorNode::Function {
                params: param_range,
                flags: FunctionFlags {
                    is_variadic: *is_variadic,
                },
                inner: inner_ref,
            }))
        }
        ParsedDeclarator::Abstract => Ok(parser
            .ast
            .parsed_types
            .alloc_decl(ParsedDeclaratorNode::Identifier { name: None })),

        ParsedDeclarator::BitField(inner, _width_expr) => {
            // BitFields inside structs are usually handled by struct parsing,
            // creating ParsedStructMember directly.
            // But if we encounter one here (rare in types?), we probably treat as identifier
            // or maybe we need to represent it.
            // For types, a bitfield declarator resolves to the underlying type declarator.
            build_parsed_declarator(parser, inner)
        }

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
    build_parsed_type_from_specifiers(parser, &specifiers, declarator.as_ref())
}
