use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_builtin_prefetch_semantic() {
    // Valid cases
    run_pass(
        "void f(int *p) { __builtin_prefetch(p); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 0); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 1); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 0, 0); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 1, 3); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(void *p) { __builtin_prefetch(p); }",
        CompilePhase::SemanticLowering,
    );

    // Invalid cases
    run_fail_with_message(
        "void f(int p) { __builtin_prefetch(p); }",
        "type mismatch: expected void*, found int",
    );
    run_fail_with_message(
        "void f(int *p) { __builtin_prefetch(p, 2); }",
        "argument 'rw' to '__builtin_prefetch' is out of range",
    );
    run_fail_with_message(
        "void f(int *p) { __builtin_prefetch(p, 0, 4); }",
        "argument 'locality' to '__builtin_prefetch' is out of range",
    );
    run_fail_with_message(
        "void f(int *p, int rw) { __builtin_prefetch(p, rw); }",
        "argument 'rw' to '__builtin_prefetch' must be a constant",
    );
}

#[test]
fn test_builtin_prefetch_pp_feature() {
    run_pass(
        "#if !__has_builtin(__builtin_prefetch)\n#error prefetch not supported\n#endif\nint main(){}",
        CompilePhase::Preprocess,
    );
}
