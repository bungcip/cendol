use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_noreturn_calling_noreturn() {
    // This should pass because abort() is noreturn, so die() does not fall off.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(void) {
            abort();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_noreturn_calling_regular() {
    // This should fail because regular() returns, so die() falls off.
    let source = r#"
        void regular(void) {}
        _Noreturn void die(void) {
            regular();
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_empty_body() {
    // This should fail because body is empty, so it falls off.
    let source = r#"
        _Noreturn void die(void) {}
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_if_else_both_noreturn() {
    // Both branches do not return, so it does not fall off.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void exit(int);
        _Noreturn void die(int c) {
            if (c) {
                abort();
            } else {
                exit(0);
            }
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_noreturn_if_only() {
    // If condition is false, it falls off.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            if (c) {
                abort();
            }
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_while_true() {
    // Current implementation treats `while` as potentially falling through.
    // So this should fail.
    let source = r#"
        _Noreturn void die(void) {
            while (1);
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_for_infinite() {
    // For loop without condition is infinite, so it does not fall off.
    let source = r#"
        _Noreturn void die(void) {
            for (;;);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_noreturn_infinite_goto() {
    // Infinite loop via goto should NOT fall off.
    let source = r#"
        _Noreturn void die(void) {
            start:
            goto start;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
