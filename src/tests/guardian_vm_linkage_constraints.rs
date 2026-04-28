use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_vla_pointer_static_storage_prohibited() {
    // C11 6.7.6.2p2: "If an identifier is declared to be an object with static
    // or thread storage duration, it shall not have a variably modified type."

    // 1. Block-scope static pointer to VLA
    run_fail_with_message(
        r#"
        void f(int n) {
            static int (*p)[n];
        }
        "#,
        "object with static storage duration shall not have a variably modified type",
    );
}

#[test]
fn test_vla_pointer_file_scope_prohibited() {
    // C11 6.7.6.2p2: "If an identifier is declared as having a variably modified type,
    // it shall ... have no linkage, and have either block scope or function prototype scope."

    // 1. File-scope pointer to VLA (external linkage)
    run_fail_with_message(
        r#"
        int n = 10;
        int (*p)[n];
        "#,
        "identifier with variably modified type shall have no linkage",
    );

    // 2. File-scope static pointer to VLA (internal linkage)
    run_fail_with_message(
        r#"
        int n = 10;
        static int (*p)[n];
        "#,
        "object with static storage duration shall not have a variably modified type",
    );
}

#[test]
fn test_vla_pointer_extern_linkage_prohibited() {
    // 1. Block-scope extern pointer to VLA (external linkage)
    run_fail_with_message(
        r#"
        void f(int n) {
            extern int (*p)[n];
        }
        "#,
        "identifier with variably modified type shall have no linkage",
    );
}

#[test]
fn test_vla_pointer_thread_local_prohibited() {
    // 1. Block-scope thread-local pointer to VLA
    run_fail_with_message(
        r#"
        void f(int n) {
            static _Thread_local int (*p)[n];
        }
        "#,
        "object with thread storage duration shall not have a variably modified type",
    );
}

#[test]
fn test_vla_pointer_block_scope_no_linkage_allowed() {
    // This is the only valid case for VM types (besides prototype scope)
    run_pass(
        r#"
        void f(int n) {
            int (*p)[n];
        }
        "#,
        CompilePhase::Mir,
    );
}
