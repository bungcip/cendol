use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_alignas_on_vla_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not appear in a declaration of
    // an identifier that is ... a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int a[n];
        }
        "#,
        "alignment specifier cannot be used on a variably modified type",
    );

    // Also prohibited for pointers to VLAs
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int (*p)[n];
        }
        "#,
        "alignment specifier cannot be used on a variably modified type",
    );
}
