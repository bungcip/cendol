//! Semantic validation tests for lvalue constraints.

use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;

fn run_lvalue_test(source: &str, expected_line: usize, expected_col: usize) {
    let config = CompileConfig::from_virtual_file(
        source.to_string(),
        crate::driver::compiler::CompilePhase::Mir,
    );
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(crate::driver::compiler::CompilePhase::Mir);

    assert!(result.is_err(), "Expected compilation to fail for source:\n{}", source);

    let diagnostics = driver.get_diagnostics();
    let error_message = "Expression is not assignable (not an lvalue)";

    let has_lvalue_error = diagnostics.iter().any(|d| {
        if d.message == error_message {
            let (line, col) = driver.source_manager.get_line_column(d.span.start).unwrap();
            assert_eq!(line, expected_line as u32, "Incorrect line number for lvalue error in source:\n{}", source);
            assert_eq!(col, expected_col as u32, "Incorrect column number for lvalue error in source:\n{}", source);
            true
        } else {
            false
        }
    });

    let actual_diagnostics: Vec<String> = diagnostics.iter().map(|d| d.message.clone()).collect();
    assert!(
        has_lvalue_error,
        "Expected '{}' error, but it was not found.\nActual diagnostics: {:?}\nFor source:\n{}",
        error_message,
        actual_diagnostics,
        source
    );
}

#[test]
fn rejects_invalid_lvalue_assignments() {
    // Assignment to a literal
    run_lvalue_test(
        r#"
        int main() {
            1 = 2;
        }
    "#, 3, 13);

    // Assignment to an arithmetic expression
    run_lvalue_test(
        r#"
        int main() {
            int x;
            x + 1 = 5;
        }
    "#, 4, 13);

    // Pre-increment on a literal
    run_lvalue_test(
        r#"
        int main() {
            ++1;
        }
    "#, 3, 13);

    // Post-increment on a literal
    run_lvalue_test(
        r#"
        int main() {
            1++;
        }
    "#, 3, 13);

    // Pre-decrement on an rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x, y;
            --(x + y);
        }
    "#, 4, 13);

    // Post-decrement on an rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x, y;
            (x + y)--;
        }
    "#, 4, 14);

    // Address-of operator on rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x;
            &(x + 1);
        }
    "#, 4, 13);
}
