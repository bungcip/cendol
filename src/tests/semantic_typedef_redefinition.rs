use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail_with_diagnostic;

#[test]
fn rejects_typedef_redefinition_with_different_type() {
    run_fail_with_diagnostic(
        r#"
typedef int T;
typedef long T;
        "#,
        CompilePhase::Mir,
        "redefinition of 'T'",
        3,
        1,
    );
}
