use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_restrict_on_function_pointer_prohibited() {
    run_fail_with_diagnostic(
        r#"
        void (* restrict f)(void);
        "#,
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        2,
        33,
    );
}

#[test]
fn test_restrict_on_non_pointer_prohibited() {
    run_fail_with_diagnostic(
        r#"
        int restrict x;
        "#,
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        2,
        9,
    );
}
