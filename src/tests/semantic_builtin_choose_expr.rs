use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_semantic_choose_expr() {
    run_pass(
        r#"
        int main() {
            int x = __builtin_choose_expr(1, 10, 20);
            int y = __builtin_choose_expr(0, 10, 20);
            return x + y;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_semantic_choose_expr_different_types() {
    run_pass(
        r#"
        int main() {
            int x = __builtin_choose_expr(1, 10, "hello");
            char *s = __builtin_choose_expr(0, 10, "hello");
            return x;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_semantic_choose_expr_lvalue() {
    run_pass(
        r#"
        int main() {
            int a = 1, b = 2;
            __builtin_choose_expr(1, a, b) = 10;
            __builtin_choose_expr(0, a, b) = 20;
            return a + b;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_semantic_choose_expr_not_constant() {
    run_fail_with_message(
        r#"
        int main() {
            int c = 1;
            return __builtin_choose_expr(c, 10, 20);
        }
        "#,
        "not a compile-time constant",
    );
}

#[test]
fn test_semantic_choose_expr_invalid_type() {
    run_fail_with_message(
        r#"
        int main() {
            return __builtin_choose_expr(1.0, 10, 20);
        }
        "#,
        "type mismatch",
    );
}
