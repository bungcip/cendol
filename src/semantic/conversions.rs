//! Implements C11 semantic conversions, such as usual arithmetic conversions
//! and integer promotions.

use crate::semantic::{BuiltinType, QualType, TypeRegistry};

/// Performs the "usual arithmetic conversions" as specified in C11 6.3.1.8.
pub(crate) fn usual_arithmetic_conversions(ctx: &TypeRegistry, lhs: QualType, rhs: QualType) -> Option<QualType> {
    let lb = lhs.ty().builtin()?;
    let rb = rhs.ty().builtin()?;

    // Floating point conversions: long double > double > float
    if lb.is_floating() || rb.is_floating() {
        let common = match (lb, rb) {
            (BuiltinType::LongDouble, _) | (_, BuiltinType::LongDouble) => ctx.type_long_double,
            (BuiltinType::Double, _) | (_, BuiltinType::Double) => ctx.type_double,
            _ => ctx.type_float,
        };
        return Some(QualType::unqualified(common));
    }

    // Both types are promoted to at least 'int' or 'unsigned int'
    let lp = integer_promotion(ctx, lhs);
    let rp = integer_promotion(ctx, rhs);
    if lp == rp {
        return Some(lp);
    }

    let lbp = lp.ty().builtin()?;
    let rbp = rp.ty().builtin()?;
    let (ls, lr) = (lbp.is_signed(), lbp.rank());
    let (rs, rr) = (rbp.is_signed(), rbp.rank());

    // Same signedness: higher rank wins
    if ls == rs {
        return Some(if lr >= rr { lp } else { rp });
    }

    // Different signedness: Higher rank usually wins; if ranks are equal, unsigned wins.
    let (ut, ur, st, sr) = if ls { (rp, rr, lp, lr) } else { (lp, lr, rp, rr) };
    if ur >= sr {
        Some(ut)
    } else {
        // If the signed type can represent all values of the unsigned type, it wins.
        // For currently supported targets (e.g. 32-bit int, 64-bit long), this holds.
        Some(st)
    }
}

/// Performs integer promotions as specified in C11 6.3.1.1.
pub(crate) fn integer_promotion(ctx: &TypeRegistry, ty: QualType) -> QualType {
    match ty.ty().builtin() {
        Some(b) if b.is_integer() && b.rank() < BuiltinType::Int.rank() => QualType::unqualified(ctx.type_int),
        _ => ty,
    }
}

/// Performs default argument promotions as specified in C11 6.5.2.2.
pub(crate) fn default_argument_promotions(ctx: &TypeRegistry, ty: QualType) -> QualType {
    match ty.ty().builtin() {
        Some(BuiltinType::Float) => QualType::unqualified(ctx.type_double),
        _ => integer_promotion(ctx, ty),
    }
}
