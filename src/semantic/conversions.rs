//! Implements C11 semantic conversions, such as usual arithmetic conversions
//! and integer promotions.

use crate::semantic::{BuiltinType, QualType, TypeRegistry};

/// Performs the "usual arithmetic conversions" as specified in C11 6.3.1.8.
pub(crate) fn usual_arithmetic_conversions(ctx: &TypeRegistry, lhs: QualType, rhs: QualType) -> Option<QualType> {
    // Floating point conversions
    if lhs.ty().builtin() == Some(BuiltinType::LongDouble) || rhs.ty().builtin() == Some(BuiltinType::LongDouble) {
        return Some(QualType::unqualified(ctx.type_long_double));
    }
    if lhs.ty().builtin() == Some(BuiltinType::Double) || rhs.ty().builtin() == Some(BuiltinType::Double) {
        return Some(QualType::unqualified(ctx.type_double));
    }
    if lhs.ty().builtin() == Some(BuiltinType::Float) || rhs.ty().builtin() == Some(BuiltinType::Float) {
        return Some(QualType::unqualified(ctx.type_float));
    }

    // Integer conversions
    let lhs_promoted = integer_promotion(ctx, lhs);
    let rhs_promoted = integer_promotion(ctx, rhs);

    if lhs_promoted.ty() == rhs_promoted.ty() {
        return Some(lhs_promoted);
    }

    let (lhs_signed, lhs_rank) = get_int_type_details(lhs_promoted.ty().builtin());
    let (rhs_signed, rhs_rank) = get_int_type_details(rhs_promoted.ty().builtin());

    if lhs_signed == rhs_signed {
        return Some(if lhs_rank >= rhs_rank {
            lhs_promoted
        } else {
            rhs_promoted
        });
    }

    if !lhs_signed && lhs_rank >= rhs_rank {
        return Some(lhs_promoted);
    }
    if !rhs_signed && rhs_rank >= lhs_rank {
        return Some(rhs_promoted);
    }

    if lhs_signed {
        if lhs_rank > rhs_rank {
            return Some(lhs_promoted);
        }
    } else if rhs_rank > lhs_rank {
        return Some(rhs_promoted);
    }

    None
}

/// Performs integer promotions as specified in C11 6.3.1.1.
pub(crate) fn integer_promotion(ctx: &TypeRegistry, ty: QualType) -> QualType {
    if let Some(builtin) = ty.ty().builtin() {
        match builtin {
            BuiltinType::Bool
            | BuiltinType::Char
            | BuiltinType::SChar
            | BuiltinType::UChar
            | BuiltinType::Short
            | BuiltinType::UShort => QualType::unqualified(ctx.type_int),
            _ => ty,
        }
    } else {
        ty
    }
}

/// Performs default argument promotions as specified in C11 6.5.2.2.
pub(crate) fn default_argument_promotions(ctx: &TypeRegistry, ty: QualType) -> QualType {
    if let Some(builtin) = ty.ty().builtin() {
        match builtin {
            BuiltinType::Float => QualType::unqualified(ctx.type_double),
            _ => integer_promotion(ctx, ty),
        }
    } else {
        ty
    }
}

fn get_int_type_details(builtin: Option<BuiltinType>) -> (bool, u8) {
    // (is_signed, rank)
    // Rank: Bool=1, Char=2, Short=3, Int=4, Long=5, LongLong=6
    match builtin {
        Some(BuiltinType::Bool) => (false, 1), // _Bool is unsigned
        Some(BuiltinType::Char) => (true, 2),  // Assuming char is signed
        Some(BuiltinType::SChar) => (true, 2),
        Some(BuiltinType::UChar) => (false, 2),
        Some(BuiltinType::Short) => (true, 3),
        Some(BuiltinType::UShort) => (false, 3),
        Some(BuiltinType::Int) => (true, 4),
        Some(BuiltinType::UInt) => (false, 4),
        Some(BuiltinType::Long) => (true, 5),
        Some(BuiltinType::ULong) => (false, 5),
        Some(BuiltinType::LongLong) => (true, 6),
        Some(BuiltinType::ULongLong) => (false, 6),
        _ => (false, 0),
    }
}
