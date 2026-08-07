use crate::tests::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
pub fn test_const_eval_logical_float_coverage() {
    let source = r#"
        extern int x;
        _Static_assert(!(0.0 && x), "float AND short circuit");
        _Static_assert(1.0 || x, "float OR short circuit");
        _Static_assert(1.0 && 1.0, "float AND true");
        _Static_assert(!(1.0 && 0.0), "float AND false");
        _Static_assert(!(0.0 || 0.0), "float OR false");
        _Static_assert(0.0 || 1.0, "float OR true");

        // UnaryOp::LogicNot on float
        _Static_assert(!0.0, "not zero");
        _Static_assert(!(!1.0), "not one");
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}
