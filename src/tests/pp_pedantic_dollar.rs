use crate::tests::test_utils::{run_pass, run_pedantic_fail_with_message, run_pedantic_pass_with_diagnostic_message};

#[test]
fn test_dollar_in_identifier_pedantic_warning() {
    let source = r#"
        int main() {
            int x$ = 1;
            return 0;
        }
    "#;
    run_pedantic_pass_with_diagnostic_message(
        source,
        crate::driver::artifact::CompilePhase::Cranelift,
        "'$' in identifier or number",
    );
}

#[test]
fn test_dollar_in_identifier_pedantic_error() {
    let source = r#"
        int main() {
            int x$ = 1;
            return 0;
        }
    "#;
    run_pedantic_fail_with_message(source, "'$' in identifier or number");
}

#[test]
fn test_dollar_in_number_pedantic_warning() {
    let source = r#"
        int main() {
            int x = 0$;
            return 0;
        }
    "#;
    // 0$ is lexed as a PP-number in C
    run_pedantic_pass_with_diagnostic_message(
        source,
        crate::driver::artifact::CompilePhase::Preprocess,
        "'$' in identifier or number",
    );
}

#[test]
fn test_dollar_in_identifier_no_pedantic() {
    let source = r#"
        int main() {
            int x$ = 1;
            return 0;
        }
    "#;
    run_pass(source, crate::driver::artifact::CompilePhase::Cranelift);
}
