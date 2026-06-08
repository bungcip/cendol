use crate::tests::test_utils::*;

#[test]
fn test_nonconstant_array_designator_rejected() {
    let source = r#"
        void test() {
            int i = 0;
            int a[2] = {[i]=1};
        }
    "#;
    run_fail_with_message(source, "expression is not an integer constant expression");
}

#[test]
fn test_constant_array_designator_accepted() {
    let source = r#"
        void test() {
            int a[2] = {[0]=1};
        }
    "#;
    run_pass(source, crate::driver::artifact::CompilePhase::Mir);
}
