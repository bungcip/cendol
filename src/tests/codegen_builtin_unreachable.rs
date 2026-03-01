use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_codegen_builtin_unreachable() {
    let source = r#"
        void test() {
            if (0) {
                __builtin_unreachable();
            }
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}
