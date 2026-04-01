use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_alignas_on_vla_prohibited() {
    // C11 6.7.5p2: "An alignment specifier shall not be used in the declaration
    // of an object that has a variably modified type."

    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int vla[n];
        }
        "#,
        "alignment specifier cannot be used on a variably modified type",
    );
}

#[test]
fn test_alignas_on_pointer_to_vla_prohibited() {
    // Pointers to VLAs are also variably modified types.
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int (*p)[n];
        }
        "#,
        "alignment specifier cannot be used on a variably modified type",
    );
}
