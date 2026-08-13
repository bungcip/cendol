use crate::tests::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_float_short_circuit_coverage() {
    let source = "
        extern int x;
        _Static_assert(!(0.0 && x), \"\");
        _Static_assert(1.0 || x, \"\");

        // Also cover the cases where evaluation doesn't short circuit but continues.
        _Static_assert(1.0 && 0.0 == 0.0, \"\");
        _Static_assert(0.0 || 1.0 == 1.0, \"\");
    ";
    run_pass(source, CompilePhase::SemanticLowering);
}
