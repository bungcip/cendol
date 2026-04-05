use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_sizeof_function_type_prohibited() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to an expression
    // that has function type... or to the parenthesized name of such a type.

    // 1. sizeof applied to a function name (expression with function type)
    run_fail_with_message(
        r#"
        void f(void);
        int main() {
            return sizeof(f);
        }
        "#,
        "Invalid application of 'sizeof' to a function type",
    );

    // 2. sizeof applied to a function type name
    run_fail_with_message(
        r#"
        int main() {
            return sizeof(void(void));
        }
        "#,
        "Invalid application of 'sizeof' to a function type",
    );
}

#[test]
fn test_alignof_function_type_prohibited() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to a function type...

    run_fail_with_message(
        r#"
        int main() {
            return _Alignof(void(void));
        }
        "#,
        "Invalid application of '_Alignof' to a function type",
    );
}

#[test]
fn test_alignof_incomplete_type_prohibited() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to... an incomplete type.

    // 1. _Alignof applied to void
    run_fail_with_message(
        r#"
        int main() {
            return _Alignof(void);
        }
        "#,
        "Invalid application of '_Alignof' to an incomplete type 'void'",
    );

    // 2. _Alignof applied to an incomplete struct
    run_fail_with_message(
        r#"
        struct S;
        int main() {
            return _Alignof(struct S);
        }
        "#,
        "Invalid application of '_Alignof' to an incomplete type 'struct S'",
    );
}

#[test]
fn test_sizeof_bitfield_prohibited() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to... a bit-field member.

    run_fail_with_message(
        r#"
        struct S {
            int x : 1;
        };
        int main() {
            struct S s;
            return sizeof(s.x);
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );
}
