use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_cast_struct_to_int() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s = {0};
            int i = (int)s;
        }
        "#,
        "scalar",
    );
}

#[test]
fn test_cast_int_to_struct() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            int i = 0;
            struct S s = (struct S)i;
        }
        "#,
        "scalar",
    );
}
