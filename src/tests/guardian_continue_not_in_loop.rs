use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_continue_not_in_loop() {
    run_fail_with_diagnostic(
        r#"
        void f(void) {
            continue;
        }
        "#,
        CompilePhase::Mir,
        "continue statement not in loop statement",
        3,
        13,
    );
}

#[test]
fn test_continue_in_if_not_in_loop() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            if (x) {
                continue;
            }
        }
        "#,
        CompilePhase::Mir,
        "continue statement not in loop statement",
        4,
        17,
    );
}

#[test]
fn test_continue_in_switch_not_in_loop() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            switch (x) {
                case 1:
                    continue;
            }
        }
        "#,
        CompilePhase::Mir,
        "continue statement not in loop statement",
        5,
        21,
    );
}

#[test]
fn test_continue_in_loop() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(void) {
            while (1) {
                continue;
            }
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_continue_in_switch_in_loop() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(int x) {
            while (1) {
                switch (x) {
                    case 1:
                        continue;
                }
            }
        }
        "#,
        CompilePhase::Mir,
    );
}
