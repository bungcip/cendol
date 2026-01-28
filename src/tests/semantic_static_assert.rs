use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail;

#[test]
fn test_static_assert_fail() {
    run_fail("void main() { _Static_assert(0, \"message\"); }", CompilePhase::Mir);
}
