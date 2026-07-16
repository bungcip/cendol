use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_guardian_invalid_atomic_specifier() {
    run_fail_with_diagnostic(
        "_Atomic(int [10]) b;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with array type",
        1,
        1,
    );

    run_fail_with_diagnostic(
        "_Atomic(void(void)) f;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with function type",
        1,
        1,
    );

    run_fail_with_diagnostic(
        "_Atomic(_Atomic int) d;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with atomic type",
        1,
        1,
    );

    run_fail_with_diagnostic(
        "_Atomic(const int) c;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with qualified type",
        1,
        1,
    );

    run_fail_with_diagnostic(
        "typedef _Atomic(void) av;",
        CompilePhase::SemanticLowering,
        "_Atomic(type-name) specifier cannot be used with void type",
        1,
        1,
    );
}

#[test]
fn test_guardian_invalid_atomic_qualifier() {
    run_fail_with_diagnostic(
        "typedef int A[10]; _Atomic A a;",
        CompilePhase::SemanticLowering,
        "_Atomic qualifier cannot be used with array type",
        1,
        20,
    );

    run_fail_with_diagnostic(
        "typedef void F(void); _Atomic F f;",
        CompilePhase::SemanticLowering,
        "_Atomic qualifier cannot be used with function type",
        1,
        23,
    );

    run_fail_with_diagnostic(
        "_Atomic void *p;",
        CompilePhase::SemanticLowering,
        "_Atomic qualifier cannot be used with void type",
        1,
        1,
    );
}
