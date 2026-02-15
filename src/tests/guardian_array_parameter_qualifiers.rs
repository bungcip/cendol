use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_array_parameter_qualifiers_pass() {
    // C11 6.7.6.3p7: a[const] is adjusted to * const a
    run_fail_with_message(
        "void f(int a[const 10]) { a = 0; }",
        CompilePhase::Mir,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_array_parameter_static_pass() {
    run_pass("void f(int a[static 10]) { }", CompilePhase::Mir);
}

#[test]
fn test_array_of_pointers_static_pass() {
    // int *a[static 10] -> array 10 of pointer to int.
    // Adjusted to: int ** const a (or similar)
    // Dimension 10 is outermost.
    run_pass("void f(int *a[static 10]) { }", CompilePhase::Mir);
}

#[test]
fn test_array_qualifiers_outside_parameter_fail() {
    run_fail_with_message(
        "int a[const 10];",
        CompilePhase::Mir,
        "type qualifiers in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_static_outside_parameter_fail() {
    run_fail_with_message(
        "int a[static 10];",
        CompilePhase::Mir,
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_static_not_outermost_fail() {
    run_fail_with_message(
        "void f(int a[10][static 5]) { }",
        CompilePhase::Mir,
        "static in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_array_qualifier_not_outermost_fail() {
    run_fail_with_message(
        "void f(int a[10][const 5]) { }",
        CompilePhase::Mir,
        "type qualifiers in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_pointer_to_array_static_fail() {
    // int (*a)[static 10] -> pointer to array 10 of int.
    // Top level is Pointer. Array is NOT outermost derivation of the parameter.
    run_fail_with_message(
        "void f(int (*a)[static 10]) { }",
        CompilePhase::Mir,
        "static in array declarator only allowed in outermost array type",
    );
}
