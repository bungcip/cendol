use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_warning_attributes_formatting() {
    let source = r#"
            void clean(int *p) {}
            typedef int __attribute__((cleanup(clean))) clean_int;
            int main() { 
                clean_int x = 0;
                return 0; 
            }
        "#;
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());

    let diagnostics = &driver.de.diagnostics;
    let warnings: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.warning_name == Some("attributes"))
        .collect();
    assert!(!warnings.is_empty(), "Should find warning tagged with attributes group");

    for warning in warnings {
        let formatted = driver.de.format_diagnostic(warning, &driver.sm);
        assert!(
            formatted.contains("[-Wattributes]"),
            "Formatted output should contain [-Wattributes]"
        );
    }
}

#[test]
fn test_warning_hash_warnings_formatting() {
    let source = r#"
            #warning This is a custom preprocessor warning
            int main() { return 0; }
        "#;
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());

    let diagnostics = &driver.de.diagnostics;
    let warnings: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.warning_name == Some("#warnings"))
        .collect();
    assert!(!warnings.is_empty(), "Should find warning tagged with #warnings group");

    for warning in warnings {
        let formatted = driver.de.format_diagnostic(warning, &driver.sm);
        assert!(
            formatted.contains("[-W#warnings]"),
            "Formatted output should contain [-W#warnings]"
        );
    }
}

#[test]
fn test_warning_builtin_macro_redefined_formatting() {
    let source = r#"
            #define __STDC__ 2
            int main() { return 0; }
        "#;
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());

    let diagnostics = &driver.de.diagnostics;
    let warnings: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.warning_name == Some("builtin-macro-redefined"))
        .collect();
    assert!(
        !warnings.is_empty(),
        "Should find warning tagged with builtin-macro-redefined group"
    );

    for warning in warnings {
        let formatted = driver.de.format_diagnostic(warning, &driver.sm);
        assert!(
            formatted.contains("[-Wbuiltin-macro-redefined]"),
            "Formatted output should contain [-Wbuiltin-macro-redefined]"
        );
    }
}
