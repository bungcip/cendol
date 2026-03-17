use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_prefetch_codegen() {
    // Should not crash during MIR generation
    run_pass("void f(int *p) { __builtin_prefetch(p, 0, 3); }", CompilePhase::Mir);
}

#[test]
fn test_builtin_prefetch_side_effects() {
    // Arguments should still be evaluated for side effects
    run_pass(
        "
        void f(int *p, int *q) {
            __builtin_prefetch(p = q, 0, 3);
        }
    ",
        CompilePhase::Mir,
    );
}
