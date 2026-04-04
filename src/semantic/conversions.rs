//! Implements C11 semantic conversions, such as usual arithmetic conversions
//! and integer promotions.

use crate::semantic::{BuiltinType, QualType, TypeKind, TypeRegistry};

/// Performs the "usual arithmetic conversions" as specified in C11 6.3.1.8.
pub(super) fn usual_arithmetic_conversions(ctx: &TypeRegistry, lhs: QualType, rhs: QualType) -> Option<QualType> {
    if lhs.is_floating() || rhs.is_floating() {
        let get_real = |qt: QualType| {
            if qt.is_complex() {
                match &ctx.get(qt.ty()).kind {
                    TypeKind::Complex { base_type } => Some(*base_type),
                    _ => unreachable!("ICE: Complex type has non-complex kind"),
                }
            } else {
                Some(qt.ty())
            }
        };

        let lr = get_real(lhs)?;
        let rr = get_real(rhs)?;

        let common_real = match (lr.builtin(), rr.builtin()) {
            (Some(BuiltinType::LongDouble), _) | (_, Some(BuiltinType::LongDouble)) => ctx.type_long_double,
            (Some(BuiltinType::Double), _) | (_, Some(BuiltinType::Double)) => ctx.type_double,
            _ => ctx.type_float,
        };

        let res_ty = if lhs.is_complex() || rhs.is_complex() {
            ctx.find_complex_type(common_real)
                .unwrap_or_else(|| panic!("ICE: complex type for {:?} not pre-allocated", common_real))
        } else {
            common_real
        };
        return Some(QualType::unqualified(res_ty));
    }

    let lp = integer_promotion(ctx, lhs, None);
    let rp = integer_promotion(ctx, rhs, None);
    if lp == rp {
        return Some(lp);
    }

    let lbp = lp.builtin()?;
    let rbp = rp.builtin()?;
    let (ls, lr) = (lbp.is_signed(), lbp.rank());
    let (rs, rr) = (rbp.is_signed(), rbp.rank());

    if ls == rs {
        return Some(if lr >= rr { lp } else { rp });
    }

    let (ut, ur, st, sr) = if ls { (rp, rr, lp, lr) } else { (lp, lr, rp, rr) };
    if ur >= sr {
        Some(ut)
    } else if ctx.get_layout(st.ty()).size > ctx.get_layout(ut.ty()).size {
        Some(st)
    } else {
        Some(QualType::unqualified(ctx.get_unsigned_corresponding_type(st.ty())))
    }
}

/// Performs integer promotions as specified in C11 6.3.1.1.
pub(super) fn integer_promotion(ctx: &TypeRegistry, qt: QualType, bitfield_width: Option<u16>) -> QualType {
    // Bolt ⚡: Fast-path for non-bitfield types that are already int or wider.
    // Integer promotion only applies to types with lower rank than int (or bitfields).
    if bitfield_width.is_none()
        && qt
            .builtin()
            .is_some_and(|b| b.is_integer() && b.rank() >= BuiltinType::Int.rank())
    {
        return qt;
    }

    if let Some(width) = bitfield_width {
        let fits = if ctx.get(qt.ty()).is_signed() {
            width <= 32
        } else {
            width < 32
        };
        return QualType::unqualified(if fits { ctx.type_int } else { ctx.type_int_unsigned });
    }

    if qt.is_enum()
        || qt
            .builtin()
            .is_some_and(|b| b.is_integer() && b.rank() < BuiltinType::Int.rank())
    {
        return QualType::unqualified(ctx.type_int);
    }
    qt
}

/// Performs default argument promotions as specified in C11 6.5.2.2.
pub(super) fn default_argument_promotions(ctx: &TypeRegistry, qt: QualType) -> QualType {
    match qt.builtin() {
        Some(BuiltinType::Float) => QualType::unqualified(ctx.type_double),
        _ => integer_promotion(ctx, qt, None),
    }
}
