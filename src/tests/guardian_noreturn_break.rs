use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_noreturn_for_break_falls_through() {
    let source = r#"
        _Noreturn void die(void) {
            for (;;) {
                break;
            }
        }
    "#;
    // This SHOULD fail but currently might pass if can_fall_through is bugged.
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_while_1_infinite() {
    let source = r#"
        _Noreturn void die(void) {
            while (1);
        }
    "#;
    // This currently fails according to existing tests, but arguably should pass.
    // However, Guardian's mission is to harden the compiler.
    // Detecting 'break' correctly is more important for correctness.
    run_pass(source, CompilePhase::Mir);
}
