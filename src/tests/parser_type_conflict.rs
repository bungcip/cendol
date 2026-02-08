use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_conflict_cast() {
    let src = "void foo() { (int struct S { int x; }) 0; }";
    run_fail_with_message(src, CompilePhase::SemanticLowering, "single type specifier");
}
