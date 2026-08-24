use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_static_assert_non_integer_type() {
    run_fail_with_message(
        r#"
        void foo() {
            _Static_assert((void*)0, "pointer should not be valid condition");
        }
        "#,
        "expected integer type"
    );
}
