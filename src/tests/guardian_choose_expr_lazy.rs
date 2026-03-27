use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_choose_expr_lazy_semantics() {
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
