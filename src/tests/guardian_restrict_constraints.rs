use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_restrict_non_pointer() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            int restrict x;
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        3,
        13,
    );
}

#[test]
fn test_restrict_function_pointer() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            void (* restrict f)(void);
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
        "restrict requires a pointer type",
        3,
        37,
    );
}

#[test]
fn test_restrict_pointer() {
    run_pass(
        r#"
        int main() {
            int * restrict p;
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
