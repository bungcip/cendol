use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_parameter_storage_static_prohibited() {
    run_fail_with_message(
        "void f(static int x) {}",
        "invalid storage class for function parameter",
    );
}

#[test]
fn test_parameter_storage_extern_prohibited() {
    run_fail_with_message(
        "void f(extern int x) {}",
        "invalid storage class for function parameter",
    );
}

#[test]
fn test_parameter_storage_auto_prohibited() {
    run_fail_with_message("void f(auto int x) {}", "invalid storage class for function parameter");
}

#[test]
fn test_parameter_storage_typedef_prohibited() {
    run_fail_with_message(
        "void f(typedef int x) {}",
        "invalid storage class for function parameter",
    );
}

#[test]
fn test_parameter_storage_thread_local_prohibited() {
    run_fail_with_message(
        "void f(_Thread_local int x) {}",
        "invalid storage class for function parameter",
    );
}

#[test]
fn test_parameter_inline_prohibited() {
    run_fail_with_message(
        "void f(inline int x) {}",
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_parameter_noreturn_prohibited() {
    run_fail_with_message(
        "void f(_Noreturn int x) {}",
        "'_Noreturn' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_parameter_register_allowed() {
    run_pass(
        r#"
        void f(register int x) {
            int y = x + 1;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_parameter_register_address_prohibited() {
    run_fail_with_message(
        r#"
        void f(register int x) {
            int *p = &x;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}
