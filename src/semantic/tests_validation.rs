//! Semantic validation tests
use crate::diagnostic::DiagnosticLevel;
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;

#[test]
fn test_static_assert_pass() {
    let config = CompileConfig::from_virtual_file(
        r#"
        int main() {
            _Static_assert(1, "This should pass");
            return 0;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        !driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_ok());
}

#[test]
fn rejects_variable_as_typedef_in_cast() {
    let config = CompileConfig::from_virtual_file(
        r#"
        int main() {
            int my_var = 10;
            (my_var) 1;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(driver.get_diagnostics().iter().any(|d| {
        d.level == DiagnosticLevel::Error
            && d.message
                .contains("Unexpected token: expected Semicolon, found IntegerConstant(1)")
    }));
    assert!(result.is_err());
}

#[test]
fn test_static_assert_fail() {
    let config = CompileConfig::from_virtual_file(
        r#"
        int main() {
            _Static_assert(0, "This should fail");
            return 0;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_err());
}

#[test]
fn test_static_assert_file_scope_fail() {
    let config = CompileConfig::from_virtual_file(
        r#"
        _Static_assert(0, "This should fail");
        int main() {
            return 0;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_err());
}

#[test]
fn test_static_assert_non_constant() {
    let config = CompileConfig::from_virtual_file(
        r#"
        int main() {
            int x = 1;
            _Static_assert(x, "error");
            return 0;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_err());
}

#[test]
fn test_static_assert_comparison() {
    let config = CompileConfig::from_virtual_file(
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
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        !driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_ok());
}

#[test]
fn test_static_assert_logical() {
    let config = CompileConfig::from_virtual_file(
        r#"
        _Static_assert(1 && 1, "This should pass");
        _Static_assert(1 || 0, "This should pass");
        _Static_assert(0 || 1, "This should pass");
        _Static_assert(!(0), "This should pass");
        int main() {
            return 0;
        }
    "#
        .to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);
    assert!(
        !driver
            .get_diagnostics()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    );
    assert!(result.is_ok());
}
