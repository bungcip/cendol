use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_restrict_on_integer_rejected() {
    run_fail_with_diagnostic(
        "int restrict x;",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        1,
        1,
    );
}

#[test]
fn test_restrict_on_array_rejected() {
    run_fail_with_diagnostic(
        "int restrict arr[5];",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        1,
        1,
    );
}

#[test]
fn test_restrict_on_function_rejected() {
    run_fail_with_diagnostic(
        "void restrict f(void);",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        1,
        1,
    );
}

#[test]
fn test_restrict_on_pointer_to_function_rejected() {
    run_fail_with_diagnostic(
        "void (* restrict f)(void);",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        1,
        25,
    );
}
