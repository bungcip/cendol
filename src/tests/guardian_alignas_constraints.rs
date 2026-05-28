use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_alignas_on_typedef_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration of a typedef
    run_fail_with_message(
        "typedef _Alignas(16) int aligned_int;",
        "alignment specifier cannot be used in a typedef",
    );
}

#[test]
fn test_alignas_on_bitfield_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration of a bit-field
    run_fail_with_message(
        r#"
        struct S {
            _Alignas(8) int x : 4;
        };
        "#,
        "alignment specifier cannot be used in a bit-field",
    );
}

#[test]
fn test_alignas_on_function_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration of a function
    run_fail_with_message(
        "_Alignas(16) void f(void);",
        "alignment specifier cannot be used in a function",
    );
}

#[test]
fn test_alignas_on_parameter_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration of a parameter
    run_fail_with_message(
        "void f(_Alignas(16) int x) {}",
        "alignment specifier cannot be used in a function parameter",
    );
}

#[test]
fn test_alignas_on_register_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration of a register
    run_fail_with_message(
        r#"
        void f(void) {
            register _Alignas(16) int x;
        }
        "#,
        "alignment specifier cannot be used in a register object",
    );
}
