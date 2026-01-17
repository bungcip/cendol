use crate::tests::semantic_common::run_fail_with_message;

use crate::driver::artifact::CompilePhase;

#[test]
fn test_noreturn_function_returns_error() {
    let a = r#"
            _Noreturn void foo() {
                return;
            }
        "#;
    run_fail_with_message(
        a,
        CompilePhase::Mir,
        "function 'foo' declared '_Noreturn' should not return",
    );
}
