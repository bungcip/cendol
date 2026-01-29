use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{run_fail, run_pass};

#[test]
fn test_static_assert_fail() {
    run_fail("void main() { _Static_assert(0, \"message\"); }", CompilePhase::Mir);
}

#[test]
fn test_static_assert_sizeof() {
    run_pass(
        "void main() { _Static_assert(sizeof(int) == 4, \"size of int is not 4\"); }",
        CompilePhase::Mir,
    );
}
