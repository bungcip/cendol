use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_static_in_typedef_array_prohibited() {
    // C11 6.7.6.2p1: "The optional type qualifiers and the keyword static shall appear
    // only in a declaration of a function parameter with an array type..."
    run_fail_with_message(
        "typedef int T[static 10];",
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_qualifiers_in_typedef_array_prohibited() {
    run_fail_with_message(
        "typedef int T[const 10];",
        "type qualifiers in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_static_in_block_scope_array_prohibited() {
    run_fail_with_message(
        "void f() { int a[static 10]; }",
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_static_in_file_scope_array_prohibited() {
    run_fail_with_message(
        "int a[static 10];",
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_static_in_function_parameter_allowed() {
    run_pass("void f(int a[static 10]);", CompilePhase::SemanticLowering);
}
