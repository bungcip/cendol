use crate::tests::test_utils::run_fail_with_diagnostic;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_cleanup_not_a_function() {
    let source = "
        int not_a_func = 42;
        void test() {
            int x __attribute__((cleanup(not_a_func)));
        }
    ";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "cleanup argument not a function", 4, 42);
}
