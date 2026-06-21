use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_break_not_in_loop_or_switch() {
    run_fail_with_diagnostic(
        r#"
        void f(void) {
            break;
        }
        "#,
        CompilePhase::Mir,
        "break statement not in loop or switch",
        3,
        13,
    );
}

#[test]
fn test_break_in_if_not_in_loop() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            if (x) {
                break;
            }
        }
        "#,
        CompilePhase::Mir,
        "break statement not in loop or switch",
        4,
        17,
    );
}

#[test]
fn test_break_in_loop() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(void) {
            while (1) {
                break;
            }
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_break_in_switch() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(int x) {
            switch (x) {
                case 1: break;
            }
        }
        "#,
        CompilePhase::Mir,
    );
}
