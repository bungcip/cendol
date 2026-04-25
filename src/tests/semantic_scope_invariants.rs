use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_function_scope_and_linkage_invariants() {
    // 1. Rejects duplicate parameter names in definition
    run_fail_with_message(r#"void f(int x, int x) {}"#, "redefinition of 'x'");

    // 2. Rejects duplicate parameter names in prototype
    run_fail_with_message(r#"void f(int x, int x);"#, "redefinition of 'x'");

    // 3. Rejects parameter redefinition in function body (C11 6.2.1p4)
    run_fail_with_message(r#"void f(int x) { int x; }"#, "redefinition of 'x'");

    // 4. Rejects local variable redefinition in same scope (C11 6.7p3)
    run_fail_with_message(r#"void f() { int x; int x; }"#, "redefinition of 'x'");

    // 5. Allows shadowing in nested blocks
    run_pass(r#"void f(int x) { { float x = 1.0; } }"#, CompilePhase::Mir);

    // 6. Correctly handles linkage inheritance (extern after static is OK)
    run_pass(r#"static void f(void); extern void f(void) {}"#, CompilePhase::Mir);

    // 7. Rejects linkage conflict (static after extern)
    run_fail_with_message(
        r#"extern void f(void); static void f(void) {}"#,
        "conflicting linkage for 'f'",
    );

    // 8. Rejects implicit __func__ redefinition
    run_fail_with_message(r#"void f() { int __func__; }"#, "Unexpected token");
}
