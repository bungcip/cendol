use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_static_assert_in_struct() {
    run_pass(
        "struct S { int x; _Static_assert(1, \"msg\"); }; int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_in_union() {
    run_pass(
        "union U { int x; _Static_assert(1, \"msg\"); }; int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_top_level() {
    run_pass(
        "_Static_assert(1, \"msg\"); int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_in_function() {
    run_pass(
        "int main() { _Static_assert(1, \"msg\"); return 0; }",
        CompilePhase::Mir,
    );
}
