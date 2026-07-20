use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_array_not_modifiable_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void foo() {
            int a[5], b[5];
            a = b;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        4,
        13,
    );
}

#[test]
fn test_function_not_modifiable_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void f(void);
        void g(void);
        void foo() {
            f = g;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        5,
        13,
    );
}

#[test]
fn test_cast_not_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void foo() {
            int a = 0;
            (long)a = 5;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        4,
        14,
    );
}

#[test]
fn test_ternary_not_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void foo() {
            int a = 0, b = 0;
            (1 ? a : b) = 5;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        4,
        14,
    );
}

#[test]
fn test_comma_not_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void foo() {
            int a = 0, b = 0;
            (a, b) = 5;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        4,
        14,
    );
}

#[test]
fn test_assignment_not_lvalue() {
    run_fail_with_diagnostic(
        r#"
        void foo() {
            int a = 0, b = 0;
            (a = b) = 5;
        }
        "#,
        CompilePhase::Mir,
        "Expression is not assignable (not an lvalue)",
        4,
        14,
    );
}
