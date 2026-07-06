use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_too_few_arguments() {
    run_fail_with_diagnostic(
        r#"
        void f(int a, int b) {}
        int main(void) {
            f(1);
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "invalid number of arguments: expected 2, found 1",
        4,
        13,
    );
}

#[test]
fn test_too_many_arguments() {
    run_fail_with_diagnostic(
        r#"
        void f(int a, int b) {}
        int main(void) {
            f(1, 2, 3);
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "invalid number of arguments: expected 2, found 3",
        4,
        13,
    );
}

#[test]
fn test_variadic_arguments_too_few() {
    run_fail_with_diagnostic(
        r#"
        void f(int a, ...);
        int main(void) {
            f();
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "invalid number of arguments: expected 1, found 0",
        4,
        13,
    );
}
