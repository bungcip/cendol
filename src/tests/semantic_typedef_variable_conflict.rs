use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail_with_diagnostic;

#[test]
fn rejects_variable_declaration_conflicting_with_typedef() {
    run_fail_with_diagnostic(
        r#"
typedef int T;
int T;
        "#,
        CompilePhase::Mir,
        "redefinition of 'T'",
        3,
        1,
    );
}

#[test]
fn rejects_typedef_declaration_conflicting_with_variable() {
    run_fail_with_diagnostic(
        r#"
int T;
typedef int T;
        "#,
        CompilePhase::Mir,
        "redefinition of 'T'",
        3,
        1,
    );
}

#[test]
fn rejects_extern_variable_declaration_conflicting_with_typedef() {
    run_fail_with_diagnostic(
        r#"
typedef int T;
extern int T;
        "#,
        CompilePhase::Mir,
        "redefinition of 'T'",
        3,
        1,
    );
}
