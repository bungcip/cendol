use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{check_diagnostic_message_only, run_pass};

/// Test multiple empty declarations
#[test]
fn test_empty_declarations_multiple() {
    let source = r#"
        char;
        char;
        int;
        int;
        int;
        
        int main() {
            return 0;
        }
    "#;

    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(&driver, "declaration does not declare anything");
    assert_eq!(driver.get_diagnostics().len(), 5);
}

/// Test empty declaration in function scope
#[test]
fn test_empty_declaration_in_function() {
    let source = r#"
        int main() {
            int;
            char;
            float;
            return 0;
        }
    "#;

    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(&driver, "declaration does not declare anything");
    assert_eq!(driver.get_diagnostics().len(), 3);
}
