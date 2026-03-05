use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_fail_with_message};

#[test]
fn test_noreturn_switch_with_default_no_fallthrough() {
    // C11 6.7.4p8: If a function is declared with the _Noreturn function specifier,
    // it shall not return to its caller.
    // If it does return, the behavior is undefined.

    // A switch with a default case where all branches are non-returning should not fall through.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            switch (c) {
                case 1: abort();
                case 2: abort();
                default: abort();
            }
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_noreturn_switch_missing_default_falls_through() {
    // If default is missing, it can fall through if no case matches.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            switch (c) {
                case 1: abort();
                case 2: abort();
            }
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_switch_with_break_falls_through() {
    // If any branch has a break, it can fall through.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            switch (c) {
                case 1: abort();
                case 2: break;
                default: abort();
            }
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_generic_selection_no_fallthrough() {
    // Generic selection branches should be considered for noreturn.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            _Generic(c,
                int: abort(),
                default: abort()
            );
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_noreturn_choose_expr_no_fallthrough() {
    // __builtin_choose_expr branches should be considered for noreturn.
    let source = r#"
        _Noreturn void abort(void);
        _Noreturn void die(int c) {
            __builtin_choose_expr(1, abort(), (void)0);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
