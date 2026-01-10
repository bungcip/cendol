// For any semantic nodes we might create? StructMember uses QualType.
use crate::ast::parsed::*;
use crate::diagnostic::SemanticError;
use crate::semantic::const_eval::ConstEvalCtx;
use crate::semantic::symbol_resolver::{LowerCtx, apply_ast_declarator, lower_decl_specifiers};
use crate::semantic::{QualType, StructMember, TypeKind};
use std::num::NonZeroU16;

/// Extracts the bit-field width from a declarator if it exists.
fn extract_bit_field_width<'a>(
    declarator: &'a ParsedDeclarator,
    ctx: &mut LowerCtx,
) -> (Option<NonZeroU16>, &'a ParsedDeclarator) {
    if let ParsedDeclarator::BitField(base, expr_ref) = declarator {
        let _const_eval_ctx = ConstEvalCtx { ast: ctx.ast };
        // expr_ref is ParsedNodeRef. ConstEval expects NodeRef.
        // TODO: We cannot eval ParsedNodeRef directly with ConstEvalCtx unless we resolve it or have ParsedConstEval.
        // For now, defer evaluation or assume 0/error.
        // Or better, we assume the expression is simple literal maybe?
        // Let's check ParsedAst for the node.
        let node = ctx.parsed_ast.get_node(*expr_ref);
        let width = if let ParsedNodeKind::LiteralInt(val) = node.kind {
            if val > 0 && val <= 64 {
                // Bitfield width can be up to type width (e.g. 64)
                NonZeroU16::new(val as u16)
            } else {
                ctx.report_error(SemanticError::InvalidBitfieldWidth { span: node.span });
                None
            }
        } else {
            // Evaluator needed for non-literals.
            ctx.report_error(SemanticError::NonConstantBitfieldWidth { span: node.span });
            None
        };
        (width, base)
    } else {
        (None, declarator)
    }
}

fn extract_identifier_from_declarator(decl: &ParsedDeclarator) -> Option<crate::ast::NameId> {
    match decl {
        ParsedDeclarator::Identifier(name, _) => Some(*name),
        ParsedDeclarator::Pointer(_, inner) => inner.as_ref().and_then(|d| extract_identifier_from_declarator(d)),
        ParsedDeclarator::Array(inner, _) => extract_identifier_from_declarator(inner),
        ParsedDeclarator::Function { inner, .. } => extract_identifier_from_declarator(inner),
        ParsedDeclarator::BitField(inner, _) => extract_identifier_from_declarator(inner),
        _ => None,
    }
}

/// Common logic for lowering struct members, used by both TypeSpecifier::Record lowering
/// and Declarator::AnonymousRecord handling.
pub(crate) fn lower_struct_members(
    members: &[ParsedDeclarationData],
    ctx: &mut LowerCtx,
    span: crate::ast::SourceSpan,
) -> Vec<StructMember> {
    let mut struct_members = Vec::new();
    for decl in members {
        // Handle anonymous struct/union members (C11 6.7.2.1p13)
        // "An unnamed member of structure or union type with no tag is called an anonymous structure or anonymous union"
        if decl.init_declarators.is_empty() {
            let spec_info = lower_decl_specifiers(&decl.specifiers, ctx, span);

            // Check for illegal storage classes
            if spec_info.storage.is_some() {
                ctx.report_error(SemanticError::ConflictingStorageClasses { span });
            }

            if let Some(type_ref) = spec_info.base_type {
                let type_ref = ctx.registry.merge_qualifiers(type_ref, spec_info.qualifiers);

                // Check if it is a Record type (struct or union)
                if type_ref.is_record() {
                    let ty = ctx.registry.get(type_ref.ty());
                    if let TypeKind::Record { tag, .. } = &ty.kind {
                        // It must have no tag to be an anonymous member
                        if tag.is_none() {
                            struct_members.push(StructMember {
                                name: None,
                                member_type: type_ref,
                                bit_field_size: None,
                                span, // Use the parent span since DeclarationData doesn't have one
                            });
                        }
                    }
                }
            }
            continue;
        }

        // Hoist declaration specifier processing out of the loop
        let spec_info = lower_decl_specifiers(&decl.specifiers, ctx, span);

        // Check for illegal storage classes
        if spec_info.storage.is_some() {
            ctx.report_error(SemanticError::ConflictingStorageClasses { span });
        }

        for init_declarator in &decl.init_declarators {
            let (bit_field_size, base_declarator) = extract_bit_field_width(&init_declarator.declarator, ctx);

            let member_name = extract_identifier_from_declarator(base_declarator);

            let member_type = if let Some(base_type_ref) = spec_info.base_type {
                // Manually re-apply qualifiers from the base type.
                let ty = apply_ast_declarator(base_type_ref.ty(), base_declarator, ctx);
                ctx.registry.merge_qualifiers(ty, spec_info.qualifiers)
            } else {
                QualType::unqualified(ctx.registry.type_int)
            };

            struct_members.push(StructMember {
                name: member_name,
                member_type,
                bit_field_size,
                span: init_declarator.span,
            });
        }
    }
    struct_members
}
