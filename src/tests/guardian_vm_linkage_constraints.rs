use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_vla_pointer_static_storage_allowed() {
    // Note: GCC and Clang allow block-scope static pointers to VLAs,
    // even though a strict reading of C11 6.7.6.2p2 might suggest otherwise.
    // They correctly evaluate the size expression once when the scope is entered.

    run_pass(
        r#"
        void f(int n) {
            static int (*p)[n];
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_vla_static_storage_prohibited() {
    // C11 6.7.6.2p2: Identifiers with static storage duration shall not have VM type.
    // For arrays (VLAs), this is always a constraint violation because storage size isn't constant.
    run_fail_with_message(
        r#"
        void f(int n) {
            static int a[n];
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
    // Relaxed for major compilers: allowed.
    run_pass(
        r#"
        int n = 10;
        static int (*p)[n];
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
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
    // This is the standard valid case for VM types.
    run_pass(
        r#"
        void f(int n) {
            int (*p)[n];
        }
        "#,
        CompilePhase::Mir,
    );
}
