use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_real_on_struct() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s;
            __real__ s;
        }
        "#,
        "Invalid operand for unary operation",
    );
}

#[test]
fn test_imag_on_struct() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s;
            __imag__ s;
        }
        "#,
        "Invalid operand for unary operation",
    );
}

#[test]
fn test_real_on_pointer() {
    run_fail_with_message(
        r#"
        int main() {
            int x;
            int *p = &x;
            __real__ p;
        }
        "#,
        "Invalid operand for unary operation",
    );
}

#[test]
fn test_imag_on_void() {
    run_fail_with_message(
        r#"
        void foo() {}
        int main() {
            __imag__ foo();
        }
        "#,
        "Invalid operand for unary operation",
    );
}
