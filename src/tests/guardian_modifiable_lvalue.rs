use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_assignment_to_incomplete_struct() {
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s1, s2;
        void f() {
            s1 = s2;
        }
        "#,
        "incomplete type",
    );
}

#[test]
fn test_assignment_to_void_lvalue() {
    run_fail_with_message(
        r#"
        void f(void *p) {
            *p = *p;
        }
        "#,
        "incomplete type",
    );
}
