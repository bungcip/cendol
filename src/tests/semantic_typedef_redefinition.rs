// Tests for C11 typedef redefinition rules.

use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail_with_diagnostic;

#[test]
fn rejects_conflicting_typedef_redefinition() {
    run_fail_with_diagnostic(
        r#"
typedef int T;
typedef float T;
        "#,
        CompilePhase::SemanticLowering,
        "redefinition of 'T' with a different type",
        3,
        1,
    );
}

use crate::tests::semantic_common::run_pass;

#[test]
fn allows_compatible_typedef_redefinition() {
    run_pass(
        r#"
typedef int T;
typedef int T;
        "#,
        CompilePhase::Mir,
    );
}
