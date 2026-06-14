use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_multiple_default_labels_rejected() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            switch (x) {
                default: break;
                case 1: break;
                default: break;
            }
        }
        "#,
        CompilePhase::Mir,
        "multiple default labels in one switch",
        6,
        17,
    );
}

#[test]
fn test_nested_switch_default_labels_allowed() {
    run_pass(
        r#"
        void f(int x, int y) {
            switch (x) {
                default:
                    switch (y) {
                        default: break;
                    }
                    break;
            }
        }
        "#,
        CompilePhase::Mir,
    );
}
