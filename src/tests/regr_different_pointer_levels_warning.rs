use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_different_pointer_levels_warning() {
    let source = r#"
        void test(void) {
            int x;
            int *y = 0;
            int *a = &x;
            const int *b = &y;
        }
    "#;
    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(
        &driver,
        "incompatible pointer types passing 'int**' to parameter of type 'const int*'",
    );
}
