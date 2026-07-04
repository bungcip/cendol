use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_auto_function_rejected() {
    run_fail_with_diagnostic(
        "auto void f(void);",
        CompilePhase::SemanticLowering,
        "invalid storage class 'auto' for function 'f'",
        1,
        1,
    );
}

#[test]
fn test_register_function_rejected() {
    run_fail_with_diagnostic(
        "register void f(void);",
        CompilePhase::SemanticLowering,
        "invalid storage class 'register' for function 'f'",
        1,
        1,
    );
}

#[test]
fn test_thread_local_function_rejected() {
    run_fail_with_diagnostic(
        "_Thread_local void f(void);",
        CompilePhase::SemanticLowering,
        "_Thread_local is not allowed here",
        1,
        1,
    );
}

#[test]
fn test_block_scope_static_function_rejected() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            static void f(void);
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
        "invalid storage class 'static' for function 'f'",
        3,
        13,
    );
}

#[test]
fn test_extern_and_static_function_accepted() {
    run_pass(
        r#"
        extern void f1(void);
        static void f2(void);
        "#,
        CompilePhase::SemanticLowering,
    );
}
