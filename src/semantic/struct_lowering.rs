use crate::ast::nodes::*;
use crate::ast::utils::extract_identifier;
use crate::diagnostic::SemanticError;
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::symbol_resolver::{LowerCtx, apply_declarator, lower_decl_specifiers};
use crate::semantic::{QualType, StructMember, TypeKind};
use std::num::NonZeroU16;

/// Extracts the bit-field width from a declarator if it exists.
fn extract_bit_field_width<'a>(declarator: &'a Declarator, ctx: &mut LowerCtx) -> (Option<NonZeroU16>, &'a Declarator) {
    if let Declarator::BitField(base, expr) = declarator {
        let const_eval_ctx = ConstEvalCtx { ast: ctx.ast };
        let width = if let Some(const_val) = const_eval::eval_const_expr(&const_eval_ctx, *expr) {
            if const_val > 0 && const_val <= 16 {
                NonZeroU16::new(const_val as u16)
            } else {
                ctx.report_error(SemanticError::InvalidBitfieldWidth {
                    span: ctx.ast.get_node(*expr).span,
                });
                None
            }
        } else {
            ctx.report_error(SemanticError::NonConstantBitfieldWidth {
                span: ctx.ast.get_node(*expr).span,
            });
            None
        };
        (width, base)
    } else {
        (None, declarator)
    }
}

/// Common logic for lowering struct members, used by both TypeSpecifier::Record lowering
/// and Declarator::AnonymousRecord handling.
pub(crate) fn lower_struct_members(
    members: &[DeclarationData],
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
                let type_ref = QualType::new(type_ref.ty(), type_ref.qualifiers() | spec_info.qualifiers);

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

            let member_name = extract_identifier(base_declarator);

            let member_type = if let Some(base_type_ref) = spec_info.base_type {
                // Manually re-apply qualifiers from the base type.
                // This is necessary because apply_declarator takes TypeRef (unqualified)
                // and effectively strips the qualifiers from the base type during type construction.
                // By re-applying them here, we ensure that qualifiers like `const` in `const int x;`
                // are preserved on the final struct member type.
                let ty = apply_declarator(base_type_ref.ty(), base_declarator, ctx);
                QualType::new(ty.ty(), ty.qualifiers() | spec_info.qualifiers)
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
