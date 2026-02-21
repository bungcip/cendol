use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_long_at_eof() {
    // This hits the simplified Long handling in type_specifiers.rs
    // and then fails in declaration parsing because no declarator/semicolon is found.
    run_fail_with_message("long", "Unexpected token");
}

#[test]
fn test_type_specifier_invalid_token() {
    // This is as close as we can get to testing "unreachable" code from C.
    // It will actually fail in the caller (declaration specifiers) because
    // it doesn't recognize '(' as a type specifier start.
    run_fail_with_message("_Atomic(", "Unexpected token");
}
