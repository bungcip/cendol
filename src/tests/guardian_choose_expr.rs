use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_builtin_choose_expr_lazy_semantics() {
    run_pass(
        r#"
        int main() {
            int x = __builtin_choose_expr(1, 42, undefined_variable);
            return x - 42;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_builtin_choose_expr_lvalue_preservation() {
    // __builtin_choose_expr should preserve lvalue-ness.
    run_pass(
        r#"
        int main() {
            int x = 0;
            __builtin_choose_expr(1, x, 1) = 10;
            return x == 10 ? 0 : 1;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_builtin_choose_expr_bitfield_constraints() {
    // __builtin_choose_expr should preserve bit-field status.
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            void *p = &__builtin_choose_expr(1, s.x, s.x);
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_builtin_choose_expr_register_constraints() {
    // __builtin_choose_expr should preserve register storage class.
    run_fail_with_message(
        r#"
        int main() {
            register int x = 0;
            void *p = &__builtin_choose_expr(1, x, x);
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_builtin_choose_expr_npc_preservation() {
    // __builtin_choose_expr should act as a null pointer constant if the selected branch is one.
    run_pass(
        r#"
        int main() {
            void *p = __builtin_choose_expr(1, 0, (void*)0);
            void *q = __builtin_choose_expr(0, (void*)0, 0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
