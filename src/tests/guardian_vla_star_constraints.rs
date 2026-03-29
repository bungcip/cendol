use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_vla_star_outside_prototype_scope() {
    // C11 6.7.6.2p4: If the size is *, the array type is a variable length array type of unspecified size,
    // which can only be used in declarations with function prototype scope.

    // 1. File scope
    run_fail_with_message("int a[*];", "[*] array size only allowed in function prototype scope");

    // 2. Block scope (not a parameter)
    run_fail_with_message(
        "void f() { int a[*]; }",
        "[*] array size only allowed in function prototype scope",
    );

    // 3. Typedef at file scope
    run_fail_with_message(
        "typedef int T[*];",
        "[*] array size only allowed in function prototype scope",
    );

    // 4. Inside function definition (not prototype scope)
    // C11 6.7.6.2p4: "In a function definition... the identifier of any such array shall
    // additionally be adjusted to a pointer type... [but] a size of * can only be used
    // in declarations with function prototype scope."
    run_fail_with_message(
        "void f(int a[*]) { }",
        "[*] array size only allowed in function prototype scope",
    );
}

#[test]
fn test_vla_star_in_prototype_scope() {
    // Valid: Function prototype
    run_pass("void f(int a[*]);", CompilePhase::SemanticLowering);

    // Valid: Abstract declarator in prototype
    run_pass("void f(int [*]);", CompilePhase::SemanticLowering);

    // Valid: Nested in pointer in prototype
    run_pass("void f(int (*p)[*]);", CompilePhase::SemanticLowering);

    // Valid: Multiple parameters
    run_pass("void f(int a[*], int b[*]);", CompilePhase::SemanticLowering);

    // Valid: prototype with qualifiers
    run_pass("void f(int a[static 10], int b[*]);", CompilePhase::SemanticLowering);
}
