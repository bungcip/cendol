use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_postfix_increment_void_pointer_prohibited() {
    run_fail_with_message("void f(void *p) { p++; }", "Invalid operand");
}

#[test]
fn test_prefix_increment_incomplete_struct_pointer_prohibited() {
    run_fail_with_message("struct S; void f(struct S *p) { ++p; }", "Invalid operand");
}

#[test]
fn test_postfix_decrement_function_pointer_prohibited() {
    run_fail_with_message("void f(void); void g() { void (*p)(void) = f; p--; }", "Invalid operand");
}

#[test]
fn test_prefix_decrement_non_scalar_prohibited() {
    run_fail_with_message("struct S { int x; }; void f(struct S s) { --s; }", "Invalid operand");
}
