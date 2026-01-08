//! Semantic validation tests for incomplete types.
use super::semantic_common::{check_diagnostic_message_only, run_fail};
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
    check_diagnostic_message_only(
        &driver,
        "Invalid application of 'sizeof' to an incomplete type",
    );
}
