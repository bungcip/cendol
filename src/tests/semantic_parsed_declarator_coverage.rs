use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_array_static_outside_parameter() {
    run_fail_with_message(
        "void f() { int s = sizeof(int[static 10]); }",
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_qualifier_outside_parameter() {
    run_fail_with_message(
        "void f() { int s = sizeof(int[const 10]); }",
        "type qualifiers in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_static_not_outermost() {
    run_fail_with_message(
        "void f(void (*p)(int[10][static 5])) { }",
        "static in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_array_qualifier_not_outermost() {
    run_fail_with_message(
        "void f(void (*p)(int[10][const 5])) { }",
        "type qualifiers in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_array_static_valid() {
    run_pass("void f(void (*p)(int[static 10])) { }", CompilePhase::SemanticLowering);
}

#[test]
fn test_array_qualifier_valid() {
    // Check that int[const 10] decays to int * const
    run_pass(
        "_Static_assert(__builtin_types_compatible_p(void (*)(int[const 10]), void (*)(int * const)), \"type mismatch\");",
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_nested_array_valid() {
    // int[static 10][5] is valid in parameter (outermost has static)
    run_pass("void f(void (*p)(int[static 10][5])) { }", CompilePhase::SemanticLowering);
}

#[test]
fn test_nested_array_decay() {
    // int[const 10][5] decays to int (* const)[5]
    run_pass(
        "_Static_assert(__builtin_types_compatible_p(void (*)(int[const 10][5]), void (*)(int (* const)[5])), \"type mismatch\");",
        CompilePhase::SemanticLowering,
    );
}
