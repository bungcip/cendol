use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail, run_pass};

#[test]
fn test_conflicting_type_specifier() {
    run_fail(
        r#"
        int float x;
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_conflicting_type_specifier_complex() {
    run_fail(
        r#"
        int _Complex x;
        "#,
        CompilePhase::SemanticLowering,
    );
}
