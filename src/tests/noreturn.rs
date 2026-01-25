//! tests for _Noreturn function specifier
use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail_with_diagnostic;

#[test]
fn test_noreturn_function_can_fall_through() {
    let src = r#"
    _Noreturn void foo() {
    }
    "#;
    run_fail_with_diagnostic(
        src,
        CompilePhase::Mir,
        "function 'foo' declared '_Noreturn' can fall off the end",
        2,
        5,
    );
}

#[test]
fn test_noreturn_function_returns() {
    let src = r#"
    _Noreturn int foo() {
        return 1;
    }
    "#;
    run_fail_with_diagnostic(
        src,
        CompilePhase::Mir,
        "function 'foo' declared '_Noreturn' contains a return statement",
        3,
        9,
    );
}

#[test]
fn test_noreturn_declaration_mismatch() {
    let src = r#"
    _Noreturn void foo();
    void foo() {
    }
    "#;
    run_fail_with_diagnostic(src, CompilePhase::SemanticLowering, "conflicting types for 'foo'", 3, 5);
}
