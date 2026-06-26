use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_case_not_in_switch() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            case 1: x = 1;
        }
        "#,
        CompilePhase::Mir,
        "'case' or 'default' label not in switch statement",
        3,
        13,
    );
}

#[test]
fn test_default_not_in_switch() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            default: x = 1;
        }
        "#,
        CompilePhase::Mir,
        "'case' or 'default' label not in switch statement",
        3,
        13,
    );
}

#[test]
fn test_case_inside_if_but_not_switch() {
    run_fail_with_diagnostic(
        r#"
        void f(int x) {
            if (x) {
                case 1: x = 1;
            }
        }
        "#,
        CompilePhase::Mir,
        "'case' or 'default' label not in switch statement",
        4,
        17,
    );
}
