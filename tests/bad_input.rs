use cendol::test_utils::compile_and_get_error;
use insta::assert_yaml_snapshot;

#[test]
fn test_unexpected_token() {
    let err = compile_and_get_error("int main() { int a = 1 +; }", "unexpected_token.c");
    assert_yaml_snapshot!("unexpected_token", err.unwrap_err());
}
