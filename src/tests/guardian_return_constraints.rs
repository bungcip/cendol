use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_void_return_with_value_span() {
    run_fail_with_diagnostic(
        r#"
        void foo(void) {
            return 42;
        }
        "#,
        CompilePhase::Mir,
        "void function 'foo' should not return a value",
        3,
        20,
    );
}

#[test]
fn test_non_void_return_without_value_span() {
    run_fail_with_diagnostic(
        r#"
        int foo(void) {
            return;
        }
        "#,
        CompilePhase::Mir,
        "non-void function 'foo' should return a value",
        3,
        13,
    );
}

#[test]
fn test_void_return_with_void_expr_span() {
    crate::tests::test_utils::run_pass_with_diagnostic(
        r#"
        void bar(void);
        void foo(void) {
            return bar();
        }
        "#,
        CompilePhase::Mir,
        "void function 'foo' should not return a value",
        4,
        20,
    );
}
