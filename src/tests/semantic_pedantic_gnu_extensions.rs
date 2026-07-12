use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_pedantic_fail_with_message, run_pedantic_pass_with_message};

#[test]
fn test_gnu_statement_expression() {
    let source = r#"
        int main() {
            int x = ({ int y = 5; y; });
            return x;
        }
    "#;

    // Test pedantic warning
    run_pedantic_pass_with_message(
        source,
        CompilePhase::SemanticLowering,
        "use of GNU statement expression extension",
    );

    // Test pedantic error
    run_pedantic_fail_with_message(source, "use of GNU statement expression extension");

    // Test no pedantic
    run_pass(source, CompilePhase::SemanticLowering);
}
