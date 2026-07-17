use crate::{
    driver::artifact::CompilePhase,
    tests::test_utils::{run_pass, run_pedantic_fail_with_message, run_pedantic_pass_with_message},
};

#[test]
fn test_directive_in_macro_args() {
    let source = r#"
        #define BUILD_ARRAY(x, y, z) { x, y, z }
        #define USE_FEATURE_B 1

        int my_array[] = BUILD_ARRAY(
            10,
        #if USE_FEATURE_B
            20,
        #else
            99,
        #endif
            30
        );
    "#;

    // Test pedantic warning
    run_pedantic_pass_with_message(
        source,
        CompilePhase::Preprocess,
        "embedding a directive within macro arguments is not portable",
    );

    // Test pedantic error
    run_pedantic_fail_with_message(source, "embedding a directive within macro arguments is not portable");

    // Test no pedantic
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_dollar_in_identifier() {
    let source = r#"
        int main() {
            int x$ = 1;
            return 0;
        }
    "#;

    // Warning
    run_pedantic_pass_with_message(source, CompilePhase::Cranelift, "'$' in identifier or number");

    // Error
    run_pedantic_fail_with_message(source, "'$' in identifier or number");

    // No pedantic
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_dollar_in_number() {
    let source = r#"
        int main() {
            int x = 0$;
            return 0;
        }
    "#;
    // 0$ is lexed as a PP-number in C
    run_pedantic_pass_with_message(source, CompilePhase::Preprocess, "'$' in identifier or number");
}
