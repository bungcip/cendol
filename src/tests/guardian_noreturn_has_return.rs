use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_noreturn_has_return() {
    run_fail_with_diagnostic(
        r#"
        _Noreturn void f(void) {
            return;
        }
        "#,
        CompilePhase::Mir,
        "function 'f' declared '_Noreturn' contains a return statement",
        3,
        13,
    );
}

#[test]
fn test_noreturn_has_return_value() {
    run_fail_with_diagnostic(
        r#"
        _Noreturn int f(void) {
            return 1;
        }
        "#,
        CompilePhase::Mir,
        "function 'f' declared '_Noreturn' contains a return statement",
        3,
        13,
    );
}
