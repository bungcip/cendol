//! Implements C11 semantic conversions, such as usual arithmetic conversions
//! and integer promotions.

use crate::{
    ast::TypeKind,
    semantic::{type_context::QualType, TypeContext},
};


/// Performs the "usual arithmetic conversions" as specified in C11 6.3.1.8.
pub fn usual_arithmetic_conversions(
    ctx: &TypeContext,
    lhs: QualType,
    rhs: QualType,
) -> Option<QualType> {
    let lhs_kind = &ctx.get(lhs.ty).kind;
    let rhs_kind = &ctx.get(rhs.ty).kind;

    match (lhs_kind, rhs_kind) {
        (TypeKind::Double { is_long_double: true }, _) | (_, TypeKind::Double { is_long_double: true }) => {
            Some(QualType::unqualified(ctx.type_long_double))
        }
        (TypeKind::Double { .. }, _) | (_, TypeKind::Double { .. }) => Some(QualType::unqualified(ctx.type_double)),
        (TypeKind::Float, _) | (_, TypeKind::Float) => Some(QualType::unqualified(ctx.type_float)),
        _ => {
            let lhs_promoted = integer_promotion(ctx, lhs);
            let rhs_promoted = integer_promotion(ctx, rhs);

            let lhs_promoted_kind = &ctx.get(lhs_promoted.ty).kind;
            let rhs_promoted_kind = &ctx.get(rhs_promoted.ty).kind;

            if lhs_promoted.ty == rhs_promoted.ty {
                return Some(lhs_promoted);
            }

            let (lhs_signed, _) = get_int_type_details(lhs_promoted_kind);
            let (rhs_signed, _) = get_int_type_details(rhs_promoted_kind);

            if lhs_signed == rhs_signed {
                return Some(if get_integer_rank(lhs_promoted_kind) >= get_integer_rank(rhs_promoted_kind) { lhs_promoted } else { rhs_promoted });
            }

            if !lhs_signed && get_integer_rank(lhs_promoted_kind) >= get_integer_rank(rhs_promoted_kind) {
                return Some(lhs_promoted);
            }
            if !rhs_signed && get_integer_rank(rhs_promoted_kind) >= get_integer_rank(lhs_promoted_kind) {
                return Some(rhs_promoted);
            }

            None
        }
    }
}

/// Performs integer promotions as specified in C11 6.3.1.1.
pub fn integer_promotion(ctx: &TypeContext, ty: QualType) -> QualType {
    let kind = &ctx.get(ty.ty).kind;
    match kind {
        TypeKind::Bool | TypeKind::Char { .. } | TypeKind::Short { .. } => {
            QualType::unqualified(ctx.type_int)
        }
        _ => ty,
    }
}

fn get_int_type_details(kind: &TypeKind) -> (bool, u8) {
    match kind {
        TypeKind::Char { is_signed } => (*is_signed, 8),
        TypeKind::Short { is_signed } => (*is_signed, 16),
        TypeKind::Int { is_signed } => (*is_signed, 32),
        TypeKind::Long { is_signed, is_long_long } => (*is_signed, if *is_long_long { 64 } else { 32 }),
        _ => (false, 0),
    }
}

fn get_integer_rank(kind: &TypeKind) -> u8 {
    match kind {
        TypeKind::Bool => 1,
        TypeKind::Char { .. } => 2,
        TypeKind::Short { .. } => 3,
        TypeKind::Int { .. } => 4,
        TypeKind::Long { .. } => 5,
        _ => 0,
    }
}
