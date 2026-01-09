//! Semantic validation tests for string literal lvalue constraints.
use super::semantic_common::{check_diagnostic, run_fail};
use crate::driver::artifact::CompilePhase;

fn run_string_lvalue_test(source: &str, expected_line: u32, expected_col: u32) {
    let driver = run_fail(source, CompilePhase::Mir);
    check_diagnostic(
        &driver,
        "cannot assign to a constant value",
        expected_line,
        expected_col,
    );
}

#[test]
fn rejects_assignment_to_string_literal() {
    run_string_lvalue_test(
        r#"
        int main() {
            "hello"[0] = 'a';
        }
    "#,
        3,
        13,
    );
}
