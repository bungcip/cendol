use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_constant_p_runtime() {
    let source = r#"
        int main() {
            int x = 5;
            const int y = 10;

            if (__builtin_constant_p(10) != 1) return 1;
            if (__builtin_constant_p(x) != 0) return 2;
            if (__builtin_constant_p(y) != 0) return 3;
            if (__builtin_constant_p(10 + 20) != 1) return 4;

            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
