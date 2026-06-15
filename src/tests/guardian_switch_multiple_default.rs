use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_switch_multiple_default() {
    let source = r#"
        int main() {
            int a = 1;
            switch(a) {
                default: break;
                default: break;
            }
        }
    "#;
    run_fail_with_message(source, "multiple default labels in one switch");
}

#[test]
fn test_switch_nested_default() {
    // Nested switch statements should allow their own default labels
    let source = r#"
        int main() {
            int a = 1;
            switch(a) {
                default:
                    switch(a) {
                        default: break;
                    }
                    break;
            }
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}
