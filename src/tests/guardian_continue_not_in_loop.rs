use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_continue_in_switch_rejected() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            switch (x) {
                case 1: continue;
            }
        }
        "#,
        CompilePhase::Mir,
        "continue statement not in loop statement",
        4,
        25,
    );
}

#[test]
fn test_continue_in_nested_switch_rejected() {
    run_fail_with_diagnostic(
        r#"
        void f(int x, int y) {
            switch (x) {
                case 1:
                    switch (y) {
                        case 2: continue;
                    }
            }
        }
        "#,
        CompilePhase::Mir,
        "continue statement not in loop statement",
        6,
        33,
    );
}

#[test]
fn test_continue_in_if_rejected() {
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
fn test_continue_valid_in_loop_in_switch() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(int x) {
            switch (x) {
                case 1:
                    while (1) {
                        continue;
                    }
            }
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_continue_valid_in_switch_in_loop() {
    crate::tests::test_utils::run_pass(
        r#"
        void f(int x) {
            while (1) {
                switch (x) {
                    case 1: continue;
                }
            }
        }
        "#,
        CompilePhase::Mir,
    );
}
