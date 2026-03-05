use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_goto_jump_into_vla_scope() {
    run_fail_with_message(
        r#"
        int main(void) {
            int n = 10;
            goto target;
            int a[n];
        target:
            return 0;
        }
        "#,
        "jump into scope of identifier with variably modified type",
    );
}

#[test]
fn test_switch_jump_into_vla_scope() {
    run_fail_with_message(
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
        "switch jumps into scope of identifier with variably modified type",
    );
}

#[test]
fn test_goto_valid_jump_vla_scope() {
    // jumping within scope or to outer scope is fine
    run_pass(
        r#"
        int main(void) {
            int n = 10;
            {
                int a[n];
            target:
                goto target;
                return 0;
            }
            goto target2;
        target2:
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
