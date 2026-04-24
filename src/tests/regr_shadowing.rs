use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_func_param_shadows_func_name() {
    run_pass(
        r#"
        int f(int f) {
            return f;
        }
        int main() {
            return f(0);
        }
        "#,
        CompilePhase::Cranelift,
    );
}
