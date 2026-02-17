use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_restrict_on_function_pointer_prohibited() {
    // C11 6.7.3p2: restrict shall be a pointer type, and the type it points to
    // shall be an object type or an incomplete type.
    // A function type is NOT an object type or an incomplete type.
    run_fail_with_message(
        r#"
        void (* restrict f)(void);
        "#,
        "restrict requires a pointer type",
    );
}

#[test]
fn test_restrict_on_non_pointer_prohibited() {
    run_fail_with_message(
        r#"
        int restrict x;
        "#,
        "restrict requires a pointer type",
    );
}
