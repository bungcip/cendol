use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_void_return_void_call() {
    run_pass(
        r#"
        void foo(void) {}
        void bar(void) {
            return foo();
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_void_return_int_call() {
    run_fail_with_message(
        r#"
        int foo(void) { return 0; }
        void bar(void) {
            return foo();
        }
    "#,
        "should not return a value",
    );
}
