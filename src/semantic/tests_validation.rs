//! Semantic validation tests
use super::tests_common::{run_fail, run_pass};
use crate::diagnostic::DiagnosticLevel;
use crate::driver::compiler::CompilePhase;

#[test]
fn test_static_assert_pass() {
    run_pass(
        r#"
        int main() {
            _Static_assert(1, "This should pass");
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_bitnot_on_non_integer() {
    let driver = run_fail(
        r#"
        int main() {
            double x = 1.0;
            ~x;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
    assert!(driver.get_diagnostics().iter().any(|d| {
        if d.level == DiagnosticLevel::Error && d.message.contains("Invalid operand for unary operation: have 'double'")
        {
            let (line, col) = driver.source_manager.get_line_column(d.span.start).unwrap();
            assert_eq!(line, 4);
            assert_eq!(col, 13);
            true
        } else {
            false
        }
    }));
}

#[test]
fn rejects_conflicting_storage_classes() {
    let driver = run_fail(
        r#"
        extern static int x;
    "#,
        CompilePhase::Mir,
    );
    assert!(driver.get_diagnostics().iter().any(|d| {
        if d.level == DiagnosticLevel::Error && d.message.contains("conflicting storage class specifiers") {
            let (line, col) = driver.source_manager.get_line_column(d.span.start).unwrap();
            assert_eq!(line, 2);
            assert_eq!(col, 9);
            true
        } else {
            false
        }
    }));
}

#[test]
fn rejects_variable_as_typedef_in_cast() {
    let driver = run_fail(
        r#"
        int main() {
            int my_var = 10;
            (my_var) 1;
        }
    "#,
        CompilePhase::Mir,
    );
    assert!(driver.get_diagnostics().iter().any(|d| {
        d.level == DiagnosticLevel::Error
            && d.message
                .contains("Unexpected token: expected Semicolon, found IntegerConstant(1)")
    }));
}

#[test]
fn test_static_assert_fail() {
    run_fail(
        r#"
        int main() {
            _Static_assert(0, "This should fail");
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_file_scope_fail() {
    run_fail(
        r#"
        _Static_assert(0, "This should fail");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_non_constant() {
    run_fail(
        r#"
        int main() {
            int x = 1;
            _Static_assert(x, "error");
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_comparison() {
    run_pass(
        r#"
        _Static_assert(1 < 2, "This should pass");
        _Static_assert(2 > 1, "This should pass");
        _Static_assert(1 == 1, "This should pass");
        _Static_assert(1 != 2, "This should pass");
        _Static_assert(1 <= 1, "This should pass");
        _Static_assert(1 >= 1, "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_logical() {
    run_pass(
        r#"
        _Static_assert(1 && 1, "This should pass");
        _Static_assert(1 || 0, "This should pass");
        _Static_assert(0 || 1, "This should pass");
        _Static_assert(!(0), "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}
