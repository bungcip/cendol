use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_compound_literal_incomplete_type() {
    run_fail_with_diagnostic(
        r#"
        struct S;
        void f() {
            (struct S){0};
        }
        "#,
        CompilePhase::Mir,
        "compound literal specifies incomplete type 'struct S'",
        4,
        13,
    );
}

#[test]
fn test_compound_literal_vla_prohibited() {
    run_fail_with_diagnostic(
        r#"
        void f(int n) {
            (int[n]){0};
        }
        "#,
        CompilePhase::Mir,
        "compound literal specifies variably modified type",
        3,
        13,
    );
}

#[test]
fn test_compound_literal_function_type_prohibited() {
    run_fail_with_diagnostic(
        r#"
        void f() {
            (void(void)){0};
        }
        "#,
        CompilePhase::Mir,
        "compound literal specifies function type",
        3,
        13,
    );
}

#[test]
fn test_compound_literal_array_unknown_size_accepted() {
    run_pass(
        r#"
        void f() {
            int *p = (int[]){1, 2, 3};
        }
        "#,
        CompilePhase::Mir,
    );
}
