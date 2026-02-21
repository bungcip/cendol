use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_valist_assignment() {
    let src = r#"
    typedef __builtin_va_list va_list;
    void foo(va_list ap) {
        va_list ap2;
        ap2 = ap;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}
