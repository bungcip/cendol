use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_restrict_on_int() {
    run_fail_with_diagnostic(
        "void test() {\n    int restrict x;\n}",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        2,
        5,
    );
}

#[test]
fn test_restrict_on_array() {
    run_fail_with_diagnostic(
        "void test() {\n    int restrict arr[5];\n}",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        2,
        5,
    );
}

#[test]
fn test_restrict_on_function() {
    run_fail_with_diagnostic(
        "void restrict f(void);",
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        1,
        1,
    );
}
