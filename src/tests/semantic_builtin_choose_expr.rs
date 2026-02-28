use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_semantic_choose_expr_basic() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, 10, 20);
            int b = __builtin_choose_expr(0, 10, 20);
            return a + b;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_type_mismatch() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(0, 10, \"hello\");
            return a;
        }
    ";
    run_fail_with_message(source, "type mismatch: expected int, found char[6]");
}

#[test]
fn test_semantic_choose_expr_const_context() {
    let source = "
        _Static_assert(__builtin_choose_expr(1, 42, 0) == 42, \"x should be 42\");
        int main() { return 0; }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_types() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, 10, \"hello\");
            char* b = __builtin_choose_expr(0, 10, \"hello\");
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_not_constant() {
    let source = "
        int main() {
            int x = 1;
            int a = __builtin_choose_expr(x, 10, 20);
            return a;
        }
    ";
    run_fail_with_message(source, "condition in '__builtin_choose_expr' is not a constant expression");
}

#[test]
fn test_semantic_choose_expr_lazy_semantic() {
    let source = "
        int main() {
            // Member 'invalid' doesn't exist on int, but it shouldn't matter since branch is not selected
            int a = __builtin_choose_expr(1, 10, ((struct {int x;})0).invalid);
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_nested() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, __builtin_choose_expr(0, 1, 2), 3);
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}
