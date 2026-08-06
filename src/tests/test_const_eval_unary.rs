use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_const_eval_unary_coverage() {
    let source = "
    void f() {
        int x = 5;
        int arr[sizeof(!x)];
    }
    ";
    run_pass(source, CompilePhase::Mir);
}
