use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_jump_into_scope_vla_goto() {
    // C11 6.8.6.1p1: A goto statement shall not jump from outside the scope of an identifier
    // having a variably modified type to inside the scope of that identifier.
    run_fail_with_diagnostic(
        r#"
        void f(int n) {
            goto label;
            int vla[n];
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
fn test_jump_into_scope_vla_switch() {
    // C11 6.8.4.2p4: A switch statement shall not jump into the scope of an identifier
    // with a variably modified type.
    run_fail_with_diagnostic(
        r#"
        void f(int n, int c) {
            switch (c) {
                int vla[n];
            case 1:
                return;
            }
        }
        "#,
        CompilePhase::Mir,
        "switch jumps into scope of identifier with variably modified type",
        5,
        13,
    );
}
