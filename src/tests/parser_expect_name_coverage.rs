use crate::tests::test_utils;

#[test]
fn test_member_access_missing_identifier() {
    // We use " . " with spaces to avoid ".1" being lexed as a float
    let source = "void f() { struct S s; s . 1; }";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found IntegerConstant");
}

#[test]
fn test_arrow_access_missing_identifier() {
    let source = "void f() { struct S *s; s->1; }";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found IntegerConstant");
}

#[test]
fn test_builtin_offsetof_missing_member() {
    let source = "void f() { __builtin_offsetof(struct S, 1); }";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found IntegerConstant");
}

#[test]
fn test_enum_missing_member() {
    let source = "enum E { 1 };";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found IntegerConstant");
}

#[test]
fn test_designated_initializer_missing_field() {
    // We use "+" to ensure it's not lexed as a float start
    let source = "struct S { int x; }; void f() { struct S s = { . + = 1 }; }";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found Plus");
}

#[test]
fn test_goto_missing_label() {
    let source = "void f() { goto 1; }";
    test_utils::run_fail_with_message(source, "Unexpected token: expected identifier, found IntegerConstant");
}
