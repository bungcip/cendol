use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_duplicate_case_rejected() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            switch (x) {
                case 1: break;
                case 1: break;
            }
        }
        "#,
        CompilePhase::Mir,
        "duplicate case value '1'",
        5,
        25,
    );
}

#[test]
fn test_nested_switch_duplicate_case_allowed() {
    run_pass(
        r#"
        void f(int x, int y) {
            switch (x) {
                case 1:
                    switch (y) {
                        case 1: break;
                    }
                    break;
            }
        }
        "#,
        CompilePhase::Mir,
    );
}
