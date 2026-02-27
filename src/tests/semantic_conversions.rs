use crate::semantic::{TypeRegistry, QualType, TypeRef};
use crate::semantic::conversions::*;

#[test]
fn test_usual_arithmetic_conversions_coverage() {
    let mut ctx = TypeRegistry::new(target_lexicon::Triple::host());

    // Test the branch where signed rank > unsigned rank,
    // and the signed type can represent all values of the unsigned type.
    // E.g., unsigned int (ur = int rank) and long long (sr = long long rank).

    let unsigned_ty = QualType::unqualified(ctx.type_int_unsigned);
    let signed_ty = QualType::unqualified(ctx.type_long_long);

    let result = usual_arithmetic_conversions(&mut ctx, unsigned_ty, signed_ty).unwrap();
    assert_eq!(result, signed_ty);

    let result2 = usual_arithmetic_conversions(&mut ctx, signed_ty, unsigned_ty).unwrap();
    assert_eq!(result2, signed_ty);

    // Test ICE: Complex type has non-complex kind
    // We want to force a panic. We need a TypeRef with TypeClass::Complex
    // Get the raw TypeRef value for int_ty
    let base = ctx.type_int.base(); // This extracts the base index (bits 0-17)

    // Construct raw value with Complex class (7)
    // base_idx (18 bits) | class (7 << 18)
    let raw_val = base | (7 << 18);

    // SAFETY: We know raw_val is not zero because base is not zero
    let forged_ty: TypeRef = unsafe { std::mem::transmute(std::num::NonZeroU32::new_unchecked(raw_val)) };

    let lhs = QualType::unqualified(forged_ty);
    let rhs = QualType::unqualified(ctx.type_float);

    // We expect a panic
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        usual_arithmetic_conversions(&mut ctx, lhs, rhs);
    }));

    assert!(result.is_err(), "Expected panic for ICE: Complex type has non-complex kind");
}
