use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{run_fail_with_message, run_pass};

#[test]
fn test_atomic_qualifier_constraints() {
    // C11 6.7.3p2: The _Atomic qualifier shall not be used with an array type or a function type.

    // 1. Array type (via typedef)
    run_fail_with_message(
        "typedef int arr[10]; _Atomic arr x;",
        CompilePhase::SemanticLowering,
        "_Atomic qualifier cannot be used with array type",
    );

    // 2. Function type (via typedef)
    run_fail_with_message(
        "typedef void func(void); _Atomic func f;",
        CompilePhase::SemanticLowering,
        "_Atomic qualifier cannot be used with function type",
    );

    // Legal case: array of atomic elements
    run_pass("_Atomic int a[10];", CompilePhase::SemanticLowering);
}

#[test]
fn test_atomic_specifier_constraints() {
    // C11 6.7.2.4p3: A type specifier of the form _Atomic ( type-name ) shall not be used
    // if the type-name is an array type, a function type, an atomic type, or a qualified type.

    // 1. Array type
    run_fail_with_message(
        "_Atomic(int [10]) b;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with array type",
    );

    // 2. Function type
    run_fail_with_message(
        "_Atomic(void(void)) f;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with function type",
    );

    // 3. Atomic type
    run_fail_with_message(
        "_Atomic(_Atomic int) d;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with atomic type",
    );

    // 4. Qualified type (const)
    run_fail_with_message(
        "_Atomic(const int) c;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with qualified type",
    );

    // 5. Qualified type (volatile)
    run_fail_with_message(
        "_Atomic(volatile int) v;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with qualified type",
    );

    // 6. Nested specifier (should be caught as atomic type)
    run_fail_with_message(
        "_Atomic(_Atomic(int)) nested;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with atomic type",
    );
}

#[test]
fn test_atomic_specifier_success() {
    // Verify that _Atomic(int) is accepted
    run_pass("_Atomic(int) x;", CompilePhase::SemanticLowering);

    // Verify that _Atomic(int) x; results in an atomic type by trying to apply it again via typedef
    run_fail_with_message(
        "typedef _Atomic(int) atomic_int; _Atomic(atomic_int) y;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with atomic type",
    );
}
