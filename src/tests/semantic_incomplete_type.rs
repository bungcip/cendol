//! Semantic validation tests for incomplete types.
use super::semantic_common::{check_diagnostic_message_only, run_fail, run_fail_with_diagnostic};
use crate::driver::artifact::CompilePhase;

#[test]
fn rejects_sizeof_on_incomplete_struct() {
    let driver = run_fail(
        r#"
        struct S;
        int main() {
            int x = sizeof(struct S);
        }
    "#,
        CompilePhase::Mir,
    );
    check_diagnostic_message_only(&driver, "Invalid application of 'sizeof' to an incomplete type");
}

#[test]
fn rejects_function_returning_incomplete_type() {
    run_fail_with_diagnostic(
        r#"
        struct S;
        struct S foo();
    "#,
        CompilePhase::Mir,
        "function has incomplete return type",
        2,
        9,
    );
}

#[test]
fn rejects_sizeof_on_incomplete_array() {
    let driver = run_fail(
        r#"
        extern int arr[];
        int main() {
            int x = sizeof(arr);
        }
    "#,
        CompilePhase::Mir,
    );
    check_diagnostic_message_only(&driver, "Invalid application of 'sizeof' to an incomplete type");
}
