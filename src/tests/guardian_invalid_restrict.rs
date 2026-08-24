use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_restrict_on_non_pointer() {
    let source = r#"
        int restrict x;
    "#;
    run_fail_with_message(source, "restrict requires a pointer type");
}

#[test]
fn test_restrict_on_function_pointer() {
    let source = r#"
        void (* restrict x)(void);
    "#;
    run_fail_with_message(source, "restrict requires a pointer type");
}

#[test]
fn test_restrict_on_array_via_typedef() {
    let source = r#"
        typedef int A[10];
        A restrict x;
    "#;
    run_fail_with_message(source, "restrict requires a pointer type");
}

#[test]
fn test_restrict_on_valid_pointer() {
    let source = r#"
        int * restrict x;
    "#;
    let _ = run_pass(source, CompilePhase::SemanticLowering);
}
