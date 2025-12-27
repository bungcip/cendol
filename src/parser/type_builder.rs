//! Type building module for the parser.
//!
//! This module contains helper functions for constructing `Type` objects
//! from parsed declaration specifiers and declarators. This logic is
//! centralized here to be used by various parts of the parser that need
//! to resolve type names (e.g., in casts, `sizeof`, `_Generic`).

use crate::ast::*;
use crate::diagnostic::ParseError;
use thin_vec::ThinVec;

use super::Parser;

/// Build a complete `TypeRef` from a set of specifiers and an optional declarator.
pub(crate) fn build_type_from_specifiers(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpecifier>,
    declarator: Option<&Declarator>,
) -> Result<TypeRef, ParseError> {
    let (base_kind, mut qualifiers) = specifiers_to_type_kind(parser, specifiers)?;

    let final_kind = if let Some(d) = declarator {
        apply_declarator_to_type(parser, base_kind, d)?
    } else {
        base_kind
    };

    if let Some(d) = declarator {
        qualifiers.insert(get_declarator_qualifiers(d));
    }

    Ok(parser.ast.push_type(Type {
        kind: final_kind,
        qualifiers,
        size: None,
        alignment: None,
    }))
}

/// Recursively apply a declarator to a base type kind to produce a new type kind.
fn apply_declarator_to_type(
    parser: &mut Parser,
    base_kind: TypeKind,
    declarator: &Declarator,
) -> Result<TypeKind, ParseError> {
    match declarator {
        Declarator::Pointer(qualifiers, inner) => {
            let pointee_kind = if let Some(inner_decl) = inner {
                apply_declarator_to_type(parser, base_kind, inner_decl)?
            } else {
                base_kind
            };
            let pointee_type_ref = parser.ast.push_type(Type {
                kind: pointee_kind,
                qualifiers: *qualifiers,
                size: None,
                alignment: None,
            });
            Ok(TypeKind::Pointer {
                pointee: pointee_type_ref,
            })
        }
        Declarator::Identifier(_, _, _) => Ok(base_kind),
        Declarator::Array(inner, size) => {
            let element_kind = apply_declarator_to_type(parser, base_kind, inner)?;
            let element_type_ref = parser.ast.push_type(Type::new(element_kind));
            Ok(TypeKind::Array {
                element_type: element_type_ref,
                size: resolve_array_size(parser, size),
            })
        }
        Declarator::Function(inner, params) => {
            let return_kind = apply_declarator_to_type(parser, base_kind, inner)?;
            let return_type_ref = parser.ast.push_type(Type::new(return_kind));
            let param_types = params
                .iter()
                .map(|p| {
                    let type_ref = build_type_from_specifiers(parser, &p.specifiers, p.declarator.as_ref())?;
                    Ok(FunctionParameter {
                        param_type: type_ref,
                        name: p.declarator.as_ref().and_then(|d| parser.get_declarator_name(d)),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;

            Ok(TypeKind::Function {
                return_type: return_type_ref,
                parameters: param_types,
                is_variadic: false, // TODO: Handle variadic functions
            })
        }
        Declarator::Abstract => Ok(base_kind),
        _ => {
            // Fallback for other declarator kinds
            Ok(base_kind)
        }
    }
}

/// Convert parsed `ArraySize` into `ArraySizeType` for the AST.
fn resolve_array_size(parser: &mut Parser, size: &ArraySize) -> ArraySizeType {
    match size {
        ArraySize::Expression { .. } => {
            // For now, we can't evaluate constant expressions at parse time,
            // so we'll treat it as a VLA with an expression.
            // This can be refined later with a constant evaluation engine.
            let type_ref = parser.ast.push_type(Type::new(TypeKind::Int { is_signed: true }));
            ArraySizeType::Variable(type_ref)
        }
        ArraySize::Star { .. } => ArraySizeType::Star,
        ArraySize::Incomplete => ArraySizeType::Incomplete,
        ArraySize::VlaSpecifier { size, .. } => {
            if size.is_some() {
                let type_ref = parser.ast.push_type(Type::new(TypeKind::Int { is_signed: true }));
                ArraySizeType::Variable(type_ref)
            } else {
                // This case should ideally not be hit if parsing is correct
                ArraySizeType::Incomplete
            }
        }
    }
}

/// Convert a list of declaration specifiers into a base type kind and qualifiers.
fn specifiers_to_type_kind(
    parser: &mut Parser,
    specifiers: &ThinVec<DeclSpecifier>,
) -> Result<(TypeKind, TypeQualifiers), ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    let mut long_count = 0;
    let mut signed_spec: Option<bool> = None;
    let mut base_type: Option<TypeKind> = None;

    for spec in specifiers {
        match spec {
            DeclSpecifier::TypeSpecifier(ts) => match ts {
                TypeSpecifier::Void => base_type = Some(TypeKind::Void),
                TypeSpecifier::Char => base_type = Some(TypeKind::Char { is_signed: true }),
                TypeSpecifier::Int => base_type = Some(TypeKind::Int { is_signed: true }),
                TypeSpecifier::Float => base_type = Some(TypeKind::Float),
                TypeSpecifier::Double => base_type = Some(TypeKind::Double { is_long_double: false }),
                TypeSpecifier::Bool => base_type = Some(TypeKind::Bool),
                TypeSpecifier::Long => long_count += 1,
                TypeSpecifier::Short => base_type = Some(TypeKind::Short { is_signed: true }),
                TypeSpecifier::Signed => signed_spec = Some(true),
                TypeSpecifier::Unsigned => signed_spec = Some(false),
                TypeSpecifier::Record(is_union, tag, def) => {
                    let is_union = *is_union;
                    let tag = *tag;

                    let (members, is_complete) = if let Some(def_data) = def {
                        // We have a definition, convert members
                        if let Some(decl_data_list) = &def_data.members {
                            let mut struct_members = Vec::new();
                            for decl in decl_data_list {
                                // For each declaration, we might have multiple declarators
                                // struct S { int a, *b; };

                                // Base type for the declaration
                                // We need to handle this carefully.
                                // If init_declarators is empty, it might be an anonymous struct member or just a type specifier?

                                if decl.init_declarators.is_empty() {
                                    // Anonymous member or just a tag?
                                    // Checks for anonymous struct/union members
                                    // For now, we only support standard members with declarators
                                    continue;
                                }

                                for init_decl in &decl.init_declarators {
                                    let member_type = build_type_from_specifiers(
                                        parser,
                                        &decl.specifiers,
                                        Some(&init_decl.declarator),
                                    )?;

                                    let name = parser
                                        .get_declarator_name(&init_decl.declarator)
                                        .unwrap_or_else(|| Symbol::from("<anon>")); // Should have name or handle bitfields/anon

                                    // TODO: Handle bitfields

                                    struct_members.push(StructMember {
                                        name,
                                        member_type,
                                        bit_field_size: None,
                                        span: SourceSpan::empty(), // TODO: Pass location
                                    });
                                }
                            }
                            (struct_members, true)
                        } else {
                            (Vec::new(), true) // Empty struct
                        }
                    } else {
                        (Vec::new(), false) // Forward declaration
                    };

                    base_type = Some(TypeKind::Record {
                        tag,
                        members,
                        is_complete,
                        is_union,
                    });
                }
                TypeSpecifier::Enum(_tag, _enumerators) => {
                    // For now, treat Enum as Int
                    // In a full implementation, we would create TypeKind::Enum
                    base_type = Some(TypeKind::Int { is_signed: true });
                }
                TypeSpecifier::TypedefName(_name) => {
                    // We need to resolve the typedef
                    // But lookup logic might be in Semantics, not Parser
                    // The parser has access to symbol table via Scope?
                    // No, Parser struct doesn't have symbol table.
                    // It constructs AST. Resolution happens in Semantics.
                    // So we create TypeKind::Typedef
                    // But TypeKind::Typedef needs aliased_type Ref.
                    // We don't have it here.
                    // So we just create a placeholder TypeKind::Typedef?
                    // Or we return a "TypedefRef" type?

                    // Semantic analysis should resolve Typedefs.
                    // Here we just create a Type representing this typedef usage.
                    // But TypeKind::Typedef definition is:
                    // Typedef { name: Symbol, aliased_type: TypeRef }
                    // We can't fill aliased_type yet.

                    // Wait, TypeKind::Typedef seems to be the DEFINTION of a typedef.
                    // Usage of a typedef should point to the underlying type?
                    // Or we need a TypeKind::TypedefReference?

                    // For now, let's treat it as Int (WRONG) or create a special handling?
                    // The current TypeKind doesn't seem to have TypedefUsage.
                    // Maybe 'Ident'?

                    // Actually, the parser resolves typedefs by looking up if an identifier is a type name.
                    // But here we are building the AST Type.

                    // Let's assume for now we only fix structs.
                    // TypedefName handling is complex if we don't have symbol table access.
                    // But we are in `type_builder.rs`.
                }
                _ => { /* Unhandled for now */ }
            },
            DeclSpecifier::TypeQualifiers(q) => qualifiers.insert(*q),
            _ => {}
        }
    }

    let base_type = base_type.unwrap_or(TypeKind::Int { is_signed: true });

    let kind = match base_type {
        TypeKind::Int { .. } | TypeKind::Short { .. } | TypeKind::Char { .. } => {
            let is_signed = signed_spec.unwrap_or(match base_type {
                TypeKind::Char { is_signed } => is_signed,
                _ => true,
            });
            if long_count == 1 {
                TypeKind::Long {
                    is_signed,
                    is_long_long: false,
                }
            } else if long_count == 2 {
                TypeKind::Long {
                    is_signed,
                    is_long_long: true,
                }
            } else {
                match base_type {
                    TypeKind::Char { .. } => TypeKind::Char { is_signed },
                    TypeKind::Short { .. } => TypeKind::Short { is_signed },
                    _ => TypeKind::Int { is_signed },
                }
            }
        }
        TypeKind::Double { .. } => {
            if long_count > 0 {
                TypeKind::Double { is_long_double: true }
            } else {
                base_type
            }
        }
        _ => base_type,
    };
    Ok((kind, qualifiers))
}

/// Recursively traverses a declarator to extract its qualifiers.
fn get_declarator_qualifiers(declarator: &Declarator) -> TypeQualifiers {
    match declarator {
        Declarator::Pointer(qualifiers, Some(inner)) => *qualifiers | get_declarator_qualifiers(inner),
        Declarator::Pointer(qualifiers, None) => *qualifiers,
        Declarator::Identifier(_, qualifiers, _) => *qualifiers,
        Declarator::Array(inner, _) => get_declarator_qualifiers(inner),
        Declarator::Function(inner, _) => get_declarator_qualifiers(inner),
        _ => TypeQualifiers::empty(),
    }
}
