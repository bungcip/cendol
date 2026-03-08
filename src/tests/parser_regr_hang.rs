use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_regr_compound_stmt_hang() {
    // Missing RightParen and RightBrace
    run_fail_with_message("int main(){main(1}", "expected )");
}

#[test]
fn test_regr_initializer_hang() {
    // Missing RightBrace in initializer list
    run_fail_with_message("void f() { int x[] = {1, 2; }", "expected }");
}

#[test]
fn test_regr_struct_hang() {
    // Missing RightBrace in struct definition
    run_fail_with_message("void f() { struct S { int x; ", "expected }");
}

#[test]
fn test_regr_params_hang() {
    // Missing RightParen in function parameters
    run_fail_with_message("int foo(int x, int y", "expected )");
}
