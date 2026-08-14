use crate::tests::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_label_addr_coverage() {
    let source = r#"
        void *f() {
            void *ptr = &&my_label;
        my_label:
            return ptr;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
