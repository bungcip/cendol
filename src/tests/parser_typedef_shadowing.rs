use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_typedef_shadowing() {
    let source = r#"
        typedef int my_type;

        int main(void) {
            float my_type = 1.0f;
            if (sizeof(my_type) != sizeof(float)) return 1;
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_typedef_param_shadowing() {
    let source = r#"
        typedef int my_type;

        int func(float my_type) {
            if (sizeof(my_type) != sizeof(float)) return 1;
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_typedef_restored_after_scope() {
    let source = r#"
        typedef int my_type;

        int func(void) {
            {
                float my_type = 1.0f;
            }
            my_type x = 42;
            return x;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
