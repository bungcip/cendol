use crate::{
    driver::artifact::CompilePhase,
    tests::test_utils::{run_fail_with_diagnostic, run_pass},
};

#[test]
fn test_register_allowed_for_parameter() {
    run_pass(
        r#"
        void f(register int x);
        int main() {
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_static_prohibited_for_parameter() {
    run_fail_with_diagnostic(
        r#"
        void f(static int x);
        "#,
        CompilePhase::SemanticLowering,
        "invalid storage class for function parameter",
        2,
        16,
    );
}

#[test]
fn test_extern_prohibited_for_parameter() {
    run_fail_with_diagnostic(
        r#"
        void f(extern int x);
        "#,
        CompilePhase::SemanticLowering,
        "invalid storage class for function parameter",
        2,
        16,
    );
}

#[test]
fn test_auto_prohibited_for_parameter() {
    run_fail_with_diagnostic(
        r#"
        void f(auto int x);
        "#,
        CompilePhase::SemanticLowering,
        "invalid storage class for function parameter",
        2,
        16,
    );
}
