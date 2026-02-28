use crate::tests::test_utils::{run_fail_with_message, run_pipeline_to_mir};

#[test]
fn test_unary_plus_minus_on_qualified_int() {
    // This targets the code path where qualifiers are stripped from the promoted type.
    // 'const int' promotes to 'const int' (no change in rank), so qualifiers persist until stripped.
    let src = r#"
        void test() {
            const int x = 1;
            int y = +x;
            int z = -x;
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_unary_plus_on_pointer() {
    // This targets the else block of is_arithmetic() for UnaryOp::Plus
    run_fail_with_message(
        r#"
        void test() {
            int *p;
            +p;
        }
        "#,
        "Invalid operand for unary operation: have 'int*'",
    );
}

#[test]
fn test_unary_minus_on_struct() {
    // This targets the else block of is_arithmetic() for UnaryOp::Minus
    run_fail_with_message(
        r#"
        struct S { int x; };
        void test() {
            struct S s;
            -s;
        }
        "#,
        "Invalid operand for unary operation: have 'struct S'",
    );
}

#[test]
fn test_invalid_inc_dec_on_arrays() {
    run_fail_with_message(
        r#"
        void test() {
            int arr[5];
            ++arr;
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );

    run_fail_with_message(
        r#"
        void test() {
            int arr[5];
            arr++;
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );

    run_fail_with_message(
        r#"
        void test() {
            ++"crash";
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );

    run_fail_with_message(
        r#"
        void test() {
            "crash"++;
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );
}

#[test]
fn test_invalid_inc_dec_on_functions() {
    run_fail_with_message(
        r#"
        void foo(void) {}
        void test() {
            ++foo;
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );

    run_fail_with_message(
        r#"
        void foo(void) {}
        void test() {
            foo++;
        }
        "#,
        "Expression is not assignable (not an lvalue)",
    );
}
