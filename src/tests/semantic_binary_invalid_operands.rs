use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_invalid_binary_operands_comparison() {
    run_fail_with_message(
        r#"
        int main() {
            int (*f)(void);
            void *p;
            f < p;
            return 0;
        }
        "#,
        "Invalid operands for binary operation: have 'int()*' and 'void*'",
    );
}
