use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_sizeof_function_type_name() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to ... the parenthesized name of [function type].
    run_fail_with_message(
        r#"
        int main() {
            return sizeof(int(int));
        }
        "#,
        "Invalid application of 'sizeof' to a function type",
    );
}

#[test]
fn test_alignof_function_type_name() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to a function type or an incomplete type.
    run_fail_with_message(
        r#"
        int main() {
            return _Alignof(int(int));
        }
        "#,
        "Invalid application of '_Alignof' to a function type",
    );
}

#[test]
fn test_alignof_incomplete_type_name() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to a function type or an incomplete type.
    run_fail_with_message(
        r#"
        int main() {
            return _Alignof(void);
        }
        "#,
        "Invalid application of '_Alignof' to an incomplete type",
    );
}

#[test]
fn test_alignof_incomplete_struct_name() {
    run_fail_with_message(
        r#"
        struct S;
        int main() {
            return _Alignof(struct S);
        }
        "#,
        "Invalid application of '_Alignof' to an incomplete type",
    );
}
