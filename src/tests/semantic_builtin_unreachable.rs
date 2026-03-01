use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_unreachable_type() {
    let source = r#"
        void test() {
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_in_noreturn() {
    // This should pass because __builtin_unreachable() means it does not fall off.
    let source = r#"
        _Noreturn void die(void) {
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_after_statement() {
    let source = r#"
        _Noreturn void die(void) {
            int x = 1;
            x++;
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_in_switch() {
    let source = r#"
        int test(int x) {
            switch (x) {
                case 1: return 10;
                default: __builtin_unreachable();
            }
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
