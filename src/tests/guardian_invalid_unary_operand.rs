use crate::{
    driver::artifact::CompilePhase,
    tests::test_utils::{run_fail_with_diagnostic},
};

#[test]
fn test_invalid_unary_operand_bitnot_float() {
    run_fail_with_diagnostic(
        r#"
        void test() {
            float f = 1.0f;
            ~f;
        }
        "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'float'",
        4,
        13,
    );
}

#[test]
fn test_invalid_unary_operand_not_arithmetic() {
    run_fail_with_diagnostic(
        r#"
        void test() {
            void *p = 0;
            +p;
        }
        "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'void*'",
        4,
        13,
    );
}

#[test]
fn test_invalid_unary_operand_increment_not_scalar() {
    run_fail_with_diagnostic(
        r#"
        struct S { int a; };
        void test() {
            struct S s;
            ++s;
        }
        "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'struct S'",
        5,
        13,
    );
}

#[test]
fn test_invalid_unary_operand_decrement_function_pointer() {
    run_fail_with_diagnostic(
        r#"
        void f(void);
        void test() {
            void (*p)(void) = f;
            --p;
        }
        "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'void()*'",
        5,
        13,
    );
}

#[test]
fn test_invalid_unary_operand_increment_incomplete_pointer() {
    run_fail_with_diagnostic(
        r#"
        void test() {
            void *p = 0;
            p++;
        }
        "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'void*'",
        4,
        13,
    );
}
