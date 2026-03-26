use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_npc_integer_constant_expression() {
    // C11 6.3.2.3p3: An integer constant expression with the value 0,
    // or such an expression cast to type void *, is called a null pointer constant.

    // 1. Literal 0 (already supported, but keep as baseline)
    run_pass(
        r#"
        void f() {
            int *p = 0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 2. Integer constant expression evaluating to 0
    run_pass(
        r#"
        void f() {
            int *p = (1 - 1);
            int *q = (0 * 5);
            int *r = (int)0.0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 3. (void*)cast of literal 0
    run_pass(
        r#"
        void f() {
            int *p = (void*)0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 4. (void*)cast of integer constant expression evaluating to 0
    run_pass(
        r#"
        void f() {
            int *p = (void*)(2 - 2);
            int *q = (void*)(0 & 1);
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 5. _Generic selection propagating NPC status
    run_pass(
        r#"
        void f() {
            int *p = _Generic(0, int: 0);
            int *q = _Generic(0, int: (1-1));
            int *r = _Generic(0, int: (void*)0);
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 6. __builtin_choose_expr propagating NPC status
    run_pass(
        r#"
        void f() {
            int *p = __builtin_choose_expr(1, 0, 1);
            int *q = __builtin_choose_expr(1, (1-1), 1);
        }
        "#,
        CompilePhase::SemanticLowering,
    );

    // 7. __real__ and __imag__ on integer constant 0
    run_pass(
        r#"
        void f() {
            int *p = __real__ 0;
            int *q = __imag__ 0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
