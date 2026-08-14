use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_extern_block_scope_initializer() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            extern int x = 10;
        }
        "#,
        CompilePhase::Mir,
        "invalid initializer",
        3,
        13,
    );
}
