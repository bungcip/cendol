use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_trap_semantic() {
    let source = r#"
        void test() {
            __builtin_trap();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_trap_noreturn() {
    let source = r#"
        void test() {
            __builtin_trap();
            int x = 1; // unreachable but semantically valid
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_trap_expression() {
    let source = r#"
        void test() {
            int x = (__builtin_trap(), 1);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
