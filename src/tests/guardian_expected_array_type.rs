use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_expected_array_type_subscript() {
    run_fail_with_diagnostic(
        r#"
        void f(int a) {
            a[0] = 1;
        }
        "#,
        CompilePhase::Mir,
        "subscripted value is not an array (have 'int')",
        3,
        13,
    );
}

#[test]
fn test_expected_array_type_subscript_struct() {
    run_fail_with_diagnostic(
        r#"
        struct S { int x; };
        void f(struct S a) {
            a[0] = 1;
        }
        "#,
        CompilePhase::Mir,
        "subscripted value is not an array (have 'struct S')",
        4,
        13,
    );
}
