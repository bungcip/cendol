use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_arithmetic_npc_propagation() {
    // C11 6.3.2.3p3: "An integer constant expression with the value 0...
    // is called a null pointer constant."
    run_pass(
        r#"
        int main() {
            void *p = 1 - 1;
            void *q = +0;
            void *r = (0 * 5);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_npc_propagation() {
    // Selection expressions should act as transparent wrappers for NPC status (DR 481).
    run_pass(
        r#"
        int main() {
            void *p = _Generic(0, int: 0);
            void *q = _Generic(1, int: (void*)0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_choose_expr_npc_propagation() {
    run_pass(
        r#"
        int main() {
            void *p = __builtin_choose_expr(1, 0, 1);
            void *q = __builtin_choose_expr(0, 1, (void*)0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}


#[test]
fn test_real_imag_npc_propagation() {
    run_pass(
        r#"
        int main() {
            void *p = __real__ 0;
            void *q = __imag__ 0;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_nested_npc_propagation() {
    run_pass(
        r#"
        int main() {
            void *p = (void*)_Generic(0, int: (1 - 1));
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
