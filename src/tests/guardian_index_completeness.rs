use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_subscript_void_pointer_prohibited() {
    // C11 6.5.2.1p1: "one of the expressions shall have type 'pointer to complete object type'..."
    // void is an incomplete type.
    run_fail_with_message(
        "void f(void *p) { (void)p[0]; }",
        "subscript of pointer to incomplete type 'void'",
    );
}

#[test]
fn test_subscript_function_pointer_prohibited() {
    // C11 6.5.2.1p1: "one of the expressions shall have type 'pointer to complete object type'..."
    // Function type is not an object type.
    run_fail_with_message(
        "void f(void); void g() { (void)(&f)[0]; }",
        "subscript of pointer to incomplete type 'void()'",
    );
}

#[test]
fn test_subscript_incomplete_struct_pointer_prohibited() {
    // C11 6.5.2.1p1: "one of the expressions shall have type 'pointer to complete object type'..."
    run_fail_with_message(
        "struct S; void f(struct S *p) { (void)p[0]; }",
        "subscript of pointer to incomplete type 'struct S'",
    );
}

#[test]
fn test_subscript_index_non_integer_prohibited() {
    // C11 6.5.2.1p1: "...and the other shall have integer type."
    run_fail_with_message(
        "void f(int *p) { (void)p[1.0]; }",
        "type mismatch: expected integer type, found double",
    );
}

#[test]
fn test_subscript_complete_object_allowed() {
    run_pass(
        "struct S { int x; }; void f(struct S *p) { (void)p[0]; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_subscript_incomplete_array_complete_element_allowed() {
    // C11 6.5.2.1p1: Subscripting is defined in terms of pointer addition.
    // Incomplete arrays decay to complete pointers.
    run_pass("extern int a[]; void f() { (void)a[0]; }", CompilePhase::Mir);
}

#[test]
fn test_subscript_commutative_allowed() {
    run_pass("void f(int *p) { (void)0[p]; }", CompilePhase::Mir);
}
