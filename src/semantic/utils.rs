use crate::{
    ast::TypeKind,
    semantic::{TypeContext, type_context::QualType},
};

pub fn is_scalar_type(ty: QualType, ctx: &TypeContext) -> bool {
    matches!(
        ctx.get(ty.ty).kind,
        TypeKind::Bool
            | TypeKind::Char { .. }
            | TypeKind::Short { .. }
            | TypeKind::Int { .. }
            | TypeKind::Long { .. }
            | TypeKind::Float
            | TypeKind::Double { .. }
            | TypeKind::Pointer { .. }
    )
}
