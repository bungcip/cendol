use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_goto_jump_into_vla_scope_span() {
    run_fail_with_diagnostic(
        r#"
        int main(void) {
            int n = 10;
            goto target;
            int a[n];
        target:
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "jump into scope of identifier with variably modified type",
        4,
        13, // span points to 'goto'
    );
}

#[test]
fn test_switch_jump_into_vla_scope_span() {
    run_fail_with_diagnostic(
        r#"
        int main(void) {
            int n = 10;
            switch(n) {
                case 1:;
                    int a[n];
                case 2:
                    return 0;
            }
        }
        "#,
        CompilePhase::Mir,
        "switch jumps into scope of identifier with variably modified type",
        8,
        21, // span points to first statement after case
    );
}
