use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_builtin_alloca_success() {
    let source = r#"
        void* test(int n) {
            return __builtin_alloca(n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_alloca_constant() {
    let source = r#"
        void* test() {
            return __builtin_alloca(100);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_alloca_invalid_arg() {
    let source = r#"
        void* test() {
            return __builtin_alloca("invalid");
        }
    "#;
    run_fail_with_message(source, "expected integer type");
}
