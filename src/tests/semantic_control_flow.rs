use super::semantic_common::setup_mir;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_goto_into_block_skips_init() {
    let source = r#"
        int printf(const char *, ...);
        void henry() {
           int a;
           goto inner;
           {
              int b;
        inner:
              b = 1234;
              printf("b = %d\n", b);
           }
           printf("done\n");
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r#"
    type %t0 = void
    type %t1 = i32
    type %t2 = i8
    type %t3 = ptr<%t2>
    type %t4 = fn(%t3, ...) -> %t1
    type %t5 = [8]%t2
    type %t6 = [8]%t2
    type %t7 = [6]%t2
    type %t8 = [6]%t2

    global @.L.str0: [8]i8 = const "b = %d\n"
    global @.L.str1: [6]i8 = const "done\n"

    fn henry() -> void
    {
      locals {
        %a: i32
        %b: i32
      }

      bb1:
        br bb2

      bb2:
        %b = const 1234
        call printf(cast<ptr<i8>>(const @.L.str0), %b)
        call printf(cast<ptr<i8>>(const @.L.str1))
        return
    }

    extern fn printf(%param0: ptr<i8>, ...) -> i32
    "#);
}

#[test]
fn test_for_loop_init_assignment() {
    let source = r#"
        int main() {
            int i;
            for (i = 0; i < 10; i++) {
                // empty body
            }
            return 0;
        }
    "#;

    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %i: i32
        %2: i32
      }

      bb1:
        %i = const 0
        br bb2

      bb2:
        %2 = %i < const 10
        cond_br %2, bb3, bb5

      bb3:
        br bb4

      bb4:
        %i = %i + const 1
        br bb2

      bb5:
        return const 0
    }
    ");
}

// Consolidated from guardian_switch_constraints.rs, guardian_noreturn_break.rs, and semantic_negative.rs
#[test]
fn test_rejects_non_integer_switch_condition() {
    use crate::tests::test_utils::run_fail_with_diagnostic;
    let source = r#"
        int main() {
            float x = 1.0f;
            switch (x) {
                case 1: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "switch condition has non-integer type 'float'",
        4,
        21,
    );
}

#[test]
fn test_rejects_non_constant_case_label() {
    use crate::tests::test_utils::run_fail_with_diagnostic;
    let source = r#"
        int main() {
            int x = 1;
            int y = 1;
            switch (x) {
                case y: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "expression in 'case' label is not an integer constant expression",
        6,
        22,
    );
}

#[test]
fn test_rejects_non_integer_case_label() {
    use crate::tests::test_utils::run_fail_with_diagnostic;
    let source = r#"
        int main() {
            switch (1) {
                case 1.0: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "expression in 'case' label is not an integer constant expression",
        4,
        22,
    );
}

#[test]
fn test_case_outside_switch() {
    run_fail_with_message(
        r#"
        int main() {
            case 1:
                break;
        }
        "#,
        "not in switch",
    );
}

#[test]
fn test_duplicate_case() {
    run_fail_with_message(
        r#"
        int main() {
            switch (1) {
                case 1: break;
                case 1: break;
            }
        }
        "#,
        "duplicate case",
    );
}

#[test]
fn test_break_outside_loop() {
    run_fail_with_message(
        r#"
        int main() {
            break;
        }
        "#,
        "break statement not in loop or switch",
    );
}

#[test]
fn test_continue_outside_loop() {
    run_fail_with_message(
        r#"
        int main() {
            continue;
        }
        "#,
        "continue statement not in loop",
    );
}

#[test]
fn test_noreturn_for_break_falls_through() {
    let source = r#"
        _Noreturn void die(void) {
            for (;;) {
                break;
            }
        }
    "#;
    run_fail_with_message(source, "function 'die' declared '_Noreturn' can fall off the end");
}

#[test]
fn test_noreturn_while_1_infinite() {
    let source = r#"
        _Noreturn void die(void) {
            while (1);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
