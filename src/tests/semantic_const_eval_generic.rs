use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_const_eval_generic() {
    let source = "
    _Static_assert(_Generic(0, int: 1, default: 2) == 1, \"\");
    _Static_assert(_Generic(0.0, int: 1, default: 2) == 2, \"\");
    ";
    run_pass(source, CompilePhase::SemanticLowering);
}
