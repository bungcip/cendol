//! Noreturn function semantic validation tests

use crate::{driver::artifact::CompilePhase, tests::test_utils::run_pipeline};

#[test]
fn test_noreturn_function_with_return() {
    let source = r#"
        _Noreturn void foo() {
            return;
        }
    "#;
    let (driver, _) = run_pipeline(source, CompilePhase::Mir);
    let diags = driver.get_diagnostics();
    assert_eq!(diags.len(), 1);
    let diag = &diags[0];
    assert_eq!(
        diag.message,
        "return statement in a function declared with \'_Noreturn\'"
    );
}

#[test]
fn test_noreturn_function_implicit_return() {
    let source = r#"
        _Noreturn void foo() {
        }
    "#;
    let (driver, _) = run_pipeline(source, CompilePhase::Mir);
    let diags = driver.get_diagnostics();
    assert_eq!(diags.len(), 1);
    let diag = &diags[0];
    assert_eq!(diag.message, "function declared with \'_Noreturn\' should not return");
}

#[test]
fn test_noreturn_function_no_return() {
    let source = r#"
        _Noreturn void foo() {
            for(;;);
        }
    "#;
    let (driver, _) = run_pipeline(source, CompilePhase::Mir);
    assert_eq!(driver.get_diagnostics().len(), 0);
}
