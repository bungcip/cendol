use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_deref_long() {
    run_fail_with_message(
        r#"
        long foo(long x) { return *x; }
        "#,
        "indirection requires pointer operand",
    );
}

#[test]
fn test_deref_int() {
    run_fail_with_message(
        r#"
        int foo(int x) { return *x; }
        "#,
        "indirection requires pointer operand",
    );
}

#[test]
fn test_deref_double() {
    run_fail_with_message(
        r#"
        double foo(double x) { return *x; }
        "#,
        "indirection requires pointer operand",
    );
}

#[test]
fn test_deref_struct() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        void foo(struct S s) { *s; }
        "#,
        "indirection requires pointer operand",
    );
}
