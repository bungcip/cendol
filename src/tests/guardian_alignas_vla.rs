use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn rejects_alignas_on_vla() {
    // C11 6.7.5p2: "An alignment specifier shall not be used in a declaration
    // of an object with a variably modified type."

    // 1. VLA
    run_fail_with_diagnostic(
        "void f(int n) { _Alignas(16) int a[n]; }",
        CompilePhase::Mir,
        "alignment specifier cannot be used in a variably modified type",
        1,
        17,
    );

    // 2. Pointer to VLA
    run_fail_with_diagnostic(
        "void f(int n) { _Alignas(16) int (*p)[n]; }",
        CompilePhase::Mir,
        "alignment specifier cannot be used in a variably modified type",
        1,
        17,
    );
}
