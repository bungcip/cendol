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
    let (base_kind, mut qualifiers) = specifiers_to_type_kind(specifiers);

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
fn specifiers_to_type_kind(specifiers: &ThinVec<DeclSpecifier>) -> (TypeKind, TypeQualifiers) {
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
    (kind, qualifiers)
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
