use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail, run_pass};

#[test]
fn guards_incomplete_types_in_declarations() {
    // 1. Tentative definitions with internal linkage (C11 6.9.2p3)
    // Shall not be an incomplete type.
    run_fail("static int arr[];", CompilePhase::SemanticLowering);
    run_fail("struct S; static struct S x;", CompilePhase::SemanticLowering);

    // 2. Objects with no linkage (C11 6.7p7)
    // Shall be complete by the end of its declarator.
    run_fail("void f() { int arr[]; }", CompilePhase::SemanticLowering);
    run_fail("void f() { static int arr[]; }", CompilePhase::SemanticLowering);
    run_fail("void f() { struct S; static struct S x; }", CompilePhase::SemanticLowering);

    // 3. Function parameters in definitions (C11 6.7.6.3p4)
    // After adjustment, parameters shall not have incomplete type.
    run_fail("void f(void x) {}", CompilePhase::SemanticLowering);
    run_fail("void f(int x, void y);", CompilePhase::SemanticLowering);

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
}
