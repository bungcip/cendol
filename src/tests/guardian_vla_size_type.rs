use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn rejects_non_integer_vla_size() {
    // C11 6.7.6.2p1: "The expression shall have an integer type."

    // Test with pointer type
    run_fail_with_diagnostic(
        "void f(void* p) { int a[p]; }",
        CompilePhase::Mir, // We use Mir to trigger full semantic analysis
        "size of array has non-integer type",
        1,
        25,
    );

    // Test with floating type (non-literal)
    run_fail_with_diagnostic(
        "void f(double d) { int a[d]; }",
        CompilePhase::Mir,
        "size of array has non-integer type",
        1,
        26,
    );
}
