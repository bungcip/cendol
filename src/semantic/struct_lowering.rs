use crate::ast::nodes::*;
use crate::ast::utils::extract_identifier;
use crate::diagnostic::SemanticError;
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::symbol_resolver::{LowerCtx, apply_declarator_for_member, lower_decl_specifiers_for_member};
use crate::semantic::{QualType, StructMember};
use std::num::NonZeroU16;

/// Extracts the bit-field width from a declarator if it exists.
fn extract_bit_field_width<'a>(
    declarator: &'a Declarator,
    ctx: &mut LowerCtx,
) -> (Option<NonZeroU16>, &'a Declarator) {
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
        for init_declarator in &decl.init_declarators {
            let (bit_field_size, base_declarator) = extract_bit_field_width(&init_declarator.declarator, ctx);

            let member_name = extract_identifier(base_declarator);

            let member_type = if let Some(base_type_ref) = lower_decl_specifiers_for_member(&decl.specifiers, ctx, span)
            {
                apply_declarator_for_member(base_type_ref.ty, base_declarator, ctx)
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
