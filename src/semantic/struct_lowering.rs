use crate::ast::nodes::*;
use crate::semantic::{QualType, StructMember};
use crate::semantic::symbol_resolver::{LowerCtx, apply_declarator_for_member, lower_decl_specifiers_for_member, process_anonymous_struct_members};
use crate::ast::utils::extract_identifier;

/// Common logic for lowering struct members, used by both TypeSpecifier::Record lowering
/// and Declarator::AnonymousRecord handling.
pub(crate) fn lower_struct_members(
    members: &[DeclarationData],
    ctx: &mut LowerCtx,
    span: crate::ast::SourceSpan,
) -> Vec<StructMember> {
    let mut struct_members = Vec::new();
    for decl in members {
        // Process anonymous struct/union members
        if decl.init_declarators.is_empty()
            && let Some((child_is_union, _, child_def)) = decl.specifiers.iter().find_map(|spec| {
                if let DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(u, t, d)) = spec {
                    Some((*u, *t, d))
                } else {
                    None
                }
            })
        {
            if let Some(d) = child_def
                && let Some(member_decls) = &d.members
            {
                let anonymous_members =
                    process_anonymous_struct_members(member_decls, child_is_union, ctx, span);
                struct_members.extend(anonymous_members);
            }
            continue;
        }

        for init_declarator in &decl.init_declarators {
            if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                let member_type = if let Some(base_type_ref) =
                    lower_decl_specifiers_for_member(&decl.specifiers, ctx, span)
                {
                    let ty = apply_declarator_for_member(
                        base_type_ref.ty,
                        &init_declarator.declarator,
                        ctx,
                    );
                    ty.ty
                } else {
                    ctx.registry.type_int
                };

                struct_members.push(StructMember {
                    name: Some(member_name),
                    member_type: QualType::unqualified(member_type),
                    bit_field_size: None,
                    span,
                });
            }
        }
    }
    struct_members
}
