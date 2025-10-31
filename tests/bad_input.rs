use cendol::test_utils::compile_and_get_error;
use insta::assert_yaml_snapshot;

#[test]
fn test_unexpected_token() {
    let err = compile_and_get_error("int main() { int a = 1 +; }", "unexpected_token.c");
    assert_yaml_snapshot!("unexpected_token", err.unwrap_err());
}

#[test]
fn test_type_mismatch() {
    let err = compile_and_get_error("int main() { int a = \"hello\"; }", "type_mismatch.c");
    assert_yaml_snapshot!("type_mismatch", err.unwrap());
}

#[test]
fn test_undefined_label() {
    let err = compile_and_get_error(
        "int main() { goto undefined_label; return 0; }",
        "undefined_label.c",
    );
    assert_yaml_snapshot!("undefined_label", err.unwrap_err());
}

#[test]
fn test_assignment_to_const() {
    let err = compile_and_get_error(
        "int main() { const int x = 10; x = 20; return x; }",
        "assignment_to_const.c",
    );
    assert_yaml_snapshot!("assignment_to_const", err.unwrap_err());
}

#[test]
fn test_duplicate_variable_declaration() {
    let err = compile_and_get_error(
        "int main() { int x = 10; int x = 20; return x; }",
        "duplicate_variable_declaration.c",
    );
    assert_yaml_snapshot!("duplicate_variable_declaration", err.unwrap_err());
}

#[test]
fn test_dereference_non_pointer() {
    let err = compile_and_get_error(
        "int main() { int x = 10; *x; return 0; }",
        "dereference_non_pointer.c",
    );
    assert_yaml_snapshot!("dereference_non_pointer", err.unwrap_err());
}

#[test]
fn test_undeclared_function() {
    let err = compile_and_get_error(
        "int main() { undeclared_function(); return 0; }",
        "undeclared_function.c",
    );
    assert_yaml_snapshot!("undeclared_function", err.unwrap_err());
}

#[test]
fn test_assignment_to_non_lvalue() {
    let err = compile_and_get_error(
        "int main() { 5 = 10; return 0; }",
        "assignment_to_non_lvalue.c",
    );
    assert_yaml_snapshot!("assignment_to_non_lvalue", err.unwrap_err());
}
