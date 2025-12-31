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
    specifiers: &ThinVec<DeclSpecifier>,
    declarator: Option<&Declarator>,
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

/// Parse base type and qualifiers from declaration specifiers
fn parse_base_type_and_qualifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpecifier>,
) -> Result<(ParsedBaseTypeRef, TypeQualifiers), ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    let mut base_type_node = None;

    for spec in specifiers {
        match spec {
            DeclSpecifier::TypeSpecifier(ts) => {
                let parsed_base = parse_type_specifier_to_parsed_base(parser, ts)?;
                base_type_node = Some(parsed_base);
            }
            DeclSpecifier::TypeQualifiers(q) => {
                qualifiers |= *q;
            }
            _ => {
                // Other specifiers (storage class, function specifiers, etc.)
                // are handled elsewhere and don't affect the base type
            }
        }
    }

    let base_type_ref = base_type_node.unwrap_or_else(|| {
        // Default to int if no type specifier found
        parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Int))
    });

    Ok((base_type_ref, qualifiers))
}

/// Convert a TypeSpecifier to a ParsedBaseTypeNode
fn parse_type_specifier_to_parsed_base(
    parser: &mut Parser,
    ts: &TypeSpecifier,
) -> Result<ParsedBaseTypeRef, ParseError> {
    match ts {
        TypeSpecifier::Void => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Void))),
        TypeSpecifier::Char => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Char))),
        TypeSpecifier::Short => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Short))),
        TypeSpecifier::Int => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Int))),
        TypeSpecifier::Long => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Long))),
        TypeSpecifier::LongLong => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::LongLong))),
        TypeSpecifier::Float => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Float))),
        TypeSpecifier::Double => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Double))),
        TypeSpecifier::LongDouble => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::LongDouble))),
        TypeSpecifier::Signed => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Signed))),
        TypeSpecifier::Unsigned => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Unsigned))),
        TypeSpecifier::Bool => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Bool))),
        TypeSpecifier::Complex => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Complex))),
        TypeSpecifier::Atomic(parsed_type) => {
            // _Atomic(type-name) - the parsed_type already contains the parsed inner type
            Ok(parser
                .ast
                .parsed_types
                .alloc_base_type(ParsedBaseTypeNode::Builtin(TypeSpecifier::Atomic(*parsed_type))))
        }
        TypeSpecifier::Record(is_union, tag, definition) => {
            let members = if let Some(def_data) = definition {
                if let Some(member_decls) = &def_data.members {
                    let mut parsed_members = Vec::new();
                    for decl in member_decls {
                        // Parse each member declaration
                        for init_decl in &decl.init_declarators {
                            if let Some(member_name) = extract_identifier(&init_decl.declarator) {
                                let member_parsed_type = build_parsed_type_from_specifiers(
                                    parser,
                                    &decl.specifiers,
                                    Some(&init_decl.declarator),
                                )?;

                                parsed_members.push(ParsedStructMember {
                                    name: member_name,
                                    ty: member_parsed_type,
                                    bit_field_size: None,
                                    span: SourceSpan::empty(), // TODO: Get proper span
                                });
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

            Ok(parser.ast.parsed_types.alloc_base_type(ParsedBaseTypeNode::Struct {
                tag: *tag,
                members,
                is_union: *is_union,
            }))
        }
        TypeSpecifier::Enum(tag, enumerators) => {
            let parsed_enumerators = if let Some(enum_node_refs) = enumerators {
                let mut parsed_enums = Vec::new();
                for &enum_ref in enum_node_refs {
                    let enum_node = parser.ast.get_node(enum_ref);
                    if let NodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
                        parsed_enums.push(ParsedEnumConstant {
                            name: *name,
                            value: value_expr_ref.as_ref().and_then(|expr_ref| {
                                // Try to evaluate constant expression
                                if let NodeKind::LiteralInt(val) = parser.ast.get_node(*expr_ref).kind {
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
        TypeSpecifier::TypedefName(name) => Ok(parser
            .ast
            .parsed_types
            .alloc_base_type(ParsedBaseTypeNode::Typedef(*name))),
    }
}

/// Build a ParsedDeclaratorNode from a Declarator
fn build_parsed_declarator(parser: &mut Parser, declarator: &Declarator) -> Result<ParsedDeclRef, ParseError> {
    match declarator {
        Declarator::Identifier(name, qualifiers, None) => {
            // Simple identifier with optional qualifiers
            if qualifiers.is_empty() {
                Ok(parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclaratorNode::Identifier { name: Some(*name) }))
            } else {
                // Create a pointer declarator with the qualifiers
                let inner = parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclaratorNode::Identifier { name: Some(*name) });
                Ok(parser.ast.parsed_types.alloc_decl(ParsedDeclaratorNode::Pointer {
                    qualifiers: *qualifiers,
                    inner,
                }))
            }
        }
        Declarator::Pointer(ptr_qualifiers, inner_decl) => {
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
        Declarator::Array(inner, size) => {
            let inner_ref = build_parsed_declarator(parser, inner)?;
            let parsed_size = convert_array_size(size)?;

            Ok(parser.ast.parsed_types.alloc_decl(ParsedDeclaratorNode::Array {
                size: parsed_size,
                inner: inner_ref,
            }))
        }
        Declarator::Function {
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

                parsed_params.push(FunctionParam {
                    name: param.declarator.as_ref().and_then(extract_identifier),
                    ty: param_parsed_type,
                    span: SourceSpan::empty(), // TODO: Get proper span
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
        Declarator::Abstract => Ok(parser
            .ast
            .parsed_types
            .alloc_decl(ParsedDeclaratorNode::Identifier { name: None })),
        _ => {
            // For unsupported declarator types, fall back to identifier
            Ok(parser
                .ast
                .parsed_types
                .alloc_decl(ParsedDeclaratorNode::Identifier { name: None }))
        }
    }
}

/// Convert ArraySize to ParsedArraySize
fn convert_array_size(size: &ArraySize) -> Result<ParsedArraySize, ParseError> {
    match size {
        ArraySize::Expression { expr, qualifiers } => Ok(ParsedArraySize::Expression {
            expr_ref: expr.get(),
            qualifiers: *qualifiers,
        }),
        ArraySize::Star { qualifiers } => Ok(ParsedArraySize::Star {
            qualifiers: *qualifiers,
        }),
        ArraySize::Incomplete => Ok(ParsedArraySize::Incomplete),
        ArraySize::VlaSpecifier {
            is_static,
            qualifiers,
            size,
        } => {
            let _ = is_static;
            // For VLA specifiers, we treat them as expressions with the size
            Ok(ParsedArraySize::Expression {
                expr_ref: size.map(|s| s.get()).unwrap_or(0),
                qualifiers: *qualifiers,
            })
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

/// Helper function to extract identifier from declarator (needed for struct members)
fn extract_identifier(declarator: &Declarator) -> Option<NameId> {
    match declarator {
        Declarator::Identifier(name, _, None) => Some(*name),
        _ => None,
    }
}
