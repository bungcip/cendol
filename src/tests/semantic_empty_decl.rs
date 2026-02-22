use crate::diagnostic::DiagnosticLevel;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

/// Test that empty declarations (e.g., `int;`) emit warnings instead of panicking
#[test]
fn test_empty_type_declaration_single() {
    let source = r#"
        int main() {
            int;
            return 0;
        }
    "#;

    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
    assert!(result.is_ok(), "Compilation should succeed with warnings");

    let diagnostics = driver.get_diagnostics();
    assert!(!diagnostics.is_empty(), "Should have at least one diagnostic");

    let warning_found = diagnostics
        .iter()
        .any(|d| d.level == DiagnosticLevel::Warning && d.message.contains("declaration does not declare anything"));
    assert!(warning_found, "Should have warning about empty declaration");
}

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

    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
    assert!(result.is_ok(), "Compilation should succeed with warnings");

    let diagnostics = driver.get_diagnostics();
    let warning_count = diagnostics
        .iter()
        .filter(|d| d.level == DiagnosticLevel::Warning && d.message.contains("declaration does not declare anything"))
        .count();

    assert_eq!(warning_count, 5, "Should have 5 warnings for empty declarations");
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

    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
    assert!(result.is_ok(), "Compilation should succeed with warnings");

    let diagnostics = driver.get_diagnostics();
    let warning_count = diagnostics
        .iter()
        .filter(|d| d.level == DiagnosticLevel::Warning && d.message.contains("declaration does not declare anything"))
        .count();

    assert_eq!(warning_count, 3, "Should have 3 warnings for empty declarations");
}

/// Test from the original issue report
#[test]
fn test_original_issue_case() {
    let source = r#"
        char;
        char;
        char;
        int;
        int;
        int;
        int;
        int;
        char foo(char *p)
        {
            char a;
            return a;
        }
        int main()
        {
            char q;
            foo(&(q));
            return 174;
        }
    "#;

    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::Mir);
    // We should successfully reach MIR generation despite the empty declarations
    assert!(
        result.is_ok(),
        "Compilation should succeed even with empty declarations"
    );

    let diagnostics = driver.get_diagnostics();
    let warning_count = diagnostics
        .iter()
        .filter(|d| d.level == DiagnosticLevel::Warning && d.message.contains("declaration does not declare anything"))
        .count();

    // 8 empty declarations at the top level
    assert_eq!(
        warning_count, 8,
        "Should have 8 warnings for empty declarations at top level"
    );
}
