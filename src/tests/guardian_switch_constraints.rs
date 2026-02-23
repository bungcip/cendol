use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn rejects_non_integer_switch_condition() {
    let source = r#"
        int main() {
            float x = 1.0f;
            switch (x) {
                case 1: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "switch condition has non-integer type 'float'",
        4,
        21,
    );
}

#[test]
fn rejects_non_constant_case_label() {
    let source = r#"
        int main() {
            int x = 1;
            int y = 1;
            switch (x) {
                case y: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "expression in 'case' label is not an integer constant expression",
        6,
22,
    );
}

#[test]
fn rejects_non_integer_case_label() {
    let source = r#"
        int main() {
            switch (1) {
                case 1.0: break;
            }
            return 0;
        }
    "#;

    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "expression in 'case' label is not an integer constant expression",
        4,
22,
    );
}

#[test]
fn visits_case_expressions_outside_switch() {
    let source = r#"
        int main() {
            case undeclared: break;
            return 0;
        }
    "#;

    // Even if outside switch, we should still catch undeclared identifier in the case expression
    // because we visit the node.
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "Undeclared identifier 'undeclared'",
        3,
18,
    );
}
