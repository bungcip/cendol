use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass_with_diagnostic};

#[test]
fn test_void_return_with_value() {
    run_fail_with_diagnostic(
        r#"
        void f(void) {
            return 1;
        }
        "#,
        CompilePhase::Mir,
        "void function 'f' should not return a value",
        3,
        20,
    );
}

#[test]
fn test_non_void_return_without_value() {
    run_fail_with_diagnostic(
        r#"
        int f(void) {
            return;
        }
        "#,
        CompilePhase::Mir,
        "non-void function 'f' should return a value",
        3,
        13,
    );
}

#[test]
fn test_void_return_with_void_expr() {
    run_pass_with_diagnostic(
        r#"
        void g(void) {}
        void f(void) {
            return g();
        }
        "#,
        CompilePhase::Mir,
        "void function 'f' should not return a value",
        4,
        20,
    );
}
