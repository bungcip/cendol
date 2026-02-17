use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn guards_incomplete_types_in_declarations() {
    // 1. Tentative definitions with internal linkage (C11 6.9.2p3)
    // Shall not be an incomplete type.
    run_fail_with_message("static int arr[];", "incomplete type 'int[]'");
    run_fail_with_message("struct S; static struct S x;", "incomplete type 'struct S'");

    // 2. Objects with no linkage (C11 6.7p7)
    // Shall be complete by the end of its declarator.
    run_fail_with_message("void f() { int arr[]; }", "incomplete type 'int[]'");
    run_fail_with_message("void f() { static int arr[]; }", "incomplete type 'int[]'");
    run_fail_with_message(
        "void f() { struct S; static struct S x; }",
        "incomplete type 'struct S'",
    );

    // 3. Function parameters in definitions (C11 6.7.6.3p4)
    // After adjustment, parameters shall not have incomplete type.
    run_fail_with_message("void f(void x) {}", "incomplete type 'void'");
    // Note: void y in a definition is also invalid if not (void)
    run_fail_with_message("void f(int x, void y) {}", "incomplete type 'void'");

    // --- Valid cases that must continue to pass ---

    // File scope tentative definition with external linkage is OK (C11 6.9.2p2)
    run_pass("int arr[]; int main() { return 0; }", CompilePhase::SemanticLowering);

    // Extern declarations can be incomplete (C11 6.7p7 exception)
    run_pass("extern int arr[];", CompilePhase::SemanticLowering);
    run_pass("void f() { extern int arr[]; }", CompilePhase::SemanticLowering);

    // (void) is a special case for no parameters (C11 6.7.6.3p10)
    run_pass("void f(void) {}", CompilePhase::SemanticLowering);

    // Array parameters decay to complete pointers
    run_pass("void f(int arr[]) {}", CompilePhase::SemanticLowering);

    // Incomplete types are ALLOWED in function prototypes (C11 6.7.6.3p12)
    run_pass("struct S; void f(struct S s);", CompilePhase::SemanticLowering);
    run_pass("void f(int arr[]);", CompilePhase::SemanticLowering);

    // Initialized arrays at block scope are OK because they are completed by initializer
    run_pass("void f() { int a[] = {1, 2, 3}; }", CompilePhase::SemanticLowering);
}
