use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_thread_local_block_scope() {
    run_fail_with_message(
        r#"
        void f() {
            _Thread_local int x;
        }
        "#,
        "_Thread_local in block scope must be combined with 'static' or 'extern'",
    );
}

#[test]
fn test_thread_local_block_scope_static() {
    run_pass(
        r#"
        void f() {
            static _Thread_local int x;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_thread_local_block_scope_extern() {
    run_pass(
        r#"
        void f() {
            extern _Thread_local int x;
        }
        "#,
        CompilePhase::Mir,
    );
}
