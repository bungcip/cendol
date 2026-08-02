use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_noreturn_function_has_return() {
    let source = r#"
        _Noreturn void die(void) {
            return;
        }
    "#;
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "function 'die' declared '_Noreturn' contains a return statement",
        3,
        13,
    );
}

#[test]
fn test_noreturn_function_has_return_with_expr() {
    let source = r#"
        _Noreturn int die(void) {
            return 1;
        }
    "#;
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "function 'die' declared '_Noreturn' contains a return statement",
        3,
        13,
    );
}
