use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_incompatible_pointer_warning_function_call() {
    let source = r#"
        void f(int *i) {
        }
        void test(void) {
            double *d;
            f(d);
        }
    "#;
    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(
        &driver,
        "incompatible pointer types passing 'double*' to parameter of type 'int*'",
    );
}
