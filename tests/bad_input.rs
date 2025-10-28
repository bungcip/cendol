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
    let err = compile_and_get_error("int main() { goto undefined_label; return 0; }", "undefined_label.c");
    assert_yaml_snapshot!("undefined_label", err.unwrap_err());
}
