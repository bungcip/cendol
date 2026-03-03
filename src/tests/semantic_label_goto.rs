use crate::tests::test_utils::*;

#[test]
fn test_goto_label_forward_backward() {
    let source = "
    int main(void) {
        goto L1;
    L1:
        goto L1;
        return 0;
    }
    ";
    run_pass(source, crate::driver::artifact::CompilePhase::Mir);
}
