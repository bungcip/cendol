use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_const_eval_statement_expr() {
    let source = "
    void f() {
        int arr[sizeof(({ int x = 5; x; }))];
    }
    ";
    run_pass(source, CompilePhase::SemanticLowering);
}
