use crate::semantic::{QualType, TypeKind, TypeRegistry};

pub fn is_scalar_type(ty: QualType, ctx: &TypeRegistry) -> bool {
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
