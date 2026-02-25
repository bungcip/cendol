use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_implicit_builtins() {
    let source = r#"
        void test() {
            float f = __builtin_nanf("");
            double d = __builtin_nan("");
            float inf_f = __builtin_inff();
            double inf = __builtin_inf();
            double huge = __builtin_huge_val();
            float huge_f = __builtin_huge_valf();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
