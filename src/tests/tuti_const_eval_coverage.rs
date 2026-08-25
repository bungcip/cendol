use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_const_eval_ternary_pointer_coverage() {
    let source = r#"
        void foo() {
            int _Static_assert_array[sizeof(1 ? (const int*)0 : (volatile int*)0)];
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
