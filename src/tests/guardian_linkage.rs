use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_extern_followed_by_static_variable_mismatch() {
    run_fail_with_message(
        r#"
        extern int x;
        static int x;
        "#,
        CompilePhase::SemanticLowering,
        "conflicting linkage",
    );
}

#[test]
fn test_static_followed_by_extern_variable_ok() {
    run_pass(
        r#"
        static int x;
        extern int x;
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_block_scope_static_shadowing_global_is_ok() {
    run_pass(
        r#"
        int x;
        void f(void) {
            static int x; // Shadows global x, no linkage conflict
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_block_scope_extern_refers_to_global_static() {
    run_pass(
        r#"
        static int x;
        void f(void) {
            extern int x;
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}


#[test]
fn test_plain_followed_by_static_variable_mismatch() {
    run_fail_with_message(
        r#"
        int x;
        static int x;
        "#,
        CompilePhase::SemanticLowering,
        "conflicting linkage",
    );
}

#[test]
fn test_static_followed_by_plain_variable_ok() {
    run_pass(
        r#"
        static int x;
        int x;
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_extern_followed_by_static_function_mismatch() {
    run_fail_with_message(
        r#"
        extern void f(void);
        static void f(void) {}
        "#,
        CompilePhase::SemanticLowering,
        "conflicting linkage",
    );
}

#[test]
fn test_static_followed_by_extern_function_ok() {
    run_pass(
        r#"
        static void f(void);
        extern void f(void);
        void f(void) {}
        "#,
        CompilePhase::SemanticLowering,
    );
}
