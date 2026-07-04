use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_goto_jump_into_vla_scope() {
    run_fail_with_diagnostic(
        r#"
        void f(int n) {
            goto label;
            int a[n];
        label:
            return;
        }
        "#,
        CompilePhase::Mir,
        "jump into scope of identifier with variably modified type",
        3,
        13,
    );
}

#[test]
fn test_switch_jump_into_vla_scope() {
    run_fail_with_diagnostic(
        r#"
        void f(int n, int x) {
            switch (x) {
                int a[n];
            case 1:
                return;
            }
        }
        "#,
        CompilePhase::Mir,
        "switch jumps into scope of identifier with variably modified type",
        6,
        17,
    );
}
