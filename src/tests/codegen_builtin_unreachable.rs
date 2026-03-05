use super::codegen_common::run_c_code_exit_status;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_codegen_builtin_unreachable() {
    let source = r#"
        void test() {
            if (0) {
                __builtin_unreachable();
            }
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_unreachable_traps() {
    // Note: We use -1 to indicate abnormal termination (like a trap/signal)
    // in our testing environment for run_c_code_exit_status.
    let code = r#"
        int main() {
            __builtin_unreachable();
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), -1);
}
