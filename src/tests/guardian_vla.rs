use crate::{
    driver::artifact::CompilePhase,
    tests::test_utils::{run_fail_with_message, run_pass},
};

#[test]
fn test_vla_non_integer_size() {
    // C11 6.7.6.2p1: "The expression shall have an integer type."

    // Test with pointer type
    run_fail_with_message("void f(void* p) { int a[p]; }", "size of array has non-integer type");

    // Test with floating type (non-literal)
    run_fail_with_message("void f(double d) { int a[d]; }", "size of array has non-integer type");
}

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

#[test]
fn test_vla_pointer_initialization() {
    // C11 6.7.9p3: "The type of the entity to be initialized shall be ... not a variable length array type."
    // A pointer to a VLA is NOT a VLA type, although it is a variably modified type.
    // So it CAN be initialized.
    run_pass("void f(int n) { int (*p)[n] = 0; }", CompilePhase::Mir);
}

#[test]
fn test_nested_vla_initialization_rejected() {
    // int a[10][n] is a VLA type because its total size is variable.
    // It should be rejected.
    run_fail_with_message(
        "void f(int n) { int a[10][n] = {0}; }",
        "variable-length array may not be initialized",
    );
}
