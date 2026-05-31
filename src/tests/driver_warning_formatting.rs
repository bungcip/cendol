use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

fn assert_warning_formatting(source: &str, warning_name: &'static str, expected_tag: &str) {
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());

    let diagnostics = &driver.de.diagnostics;
    let warnings: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.warning_name == Some(warning_name))
        .collect();
    assert!(
        !warnings.is_empty(),
        "Should find warning tagged with {} group",
        warning_name
    );

    for warning in warnings {
        let mut formatted = String::new();
        driver
            .de
            .print_single(warning, &driver.sm, &mut formatted)
            .unwrap();
        assert!(
            formatted.contains(expected_tag),
            "Formatted output should contain {}",
            expected_tag
        );
    }
}

#[test]
fn test_warning_attributes_formatting() {
    assert_warning_formatting(
        r#"
            void clean(int *p) {}
            typedef int __attribute__((cleanup(clean))) clean_int;
            int main() { 
                clean_int x = 0;
                return 0; 
            }
        "#,
        "attributes",
        "[-Wattributes]",
    );
}

#[test]
fn test_warning_hash_warnings_formatting() {
    assert_warning_formatting(
        r#"
            #warning This is a custom preprocessor warning
            int main() { return 0; }
        "#,
        "#warnings",
        "[-W#warnings]",
    );
}

#[test]
fn test_warning_builtin_macro_redefined_formatting() {
    assert_warning_formatting(
        r#"
            #define __STDC__ 2
            int main() { return 0; }
        "#,
        "builtin-macro-redefined",
        "[-Wbuiltin-macro-redefined]",
    );
}

#[test]
fn test_diagnostic_engine_writer() {
    use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
    use crate::source_manager::{SourceManager, SourceSpan};

    let mut de = DiagnosticEngine::default();
    let sm = SourceManager::new();

    struct SharedBuffer(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);
    impl std::io::Write for SharedBuffer {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().write(buf)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.0.lock().unwrap().flush()
        }
    }

    let raw_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let writer = SharedBuffer(raw_buf.clone());
    de.set_writer(Box::new(writer));

    de.report_diagnostic(Diagnostic {
        level: DiagnosticLevel::Note,
        message: "Test custom note".to_string(),
        span: SourceSpan::default(),
        hints: Vec::new(),
        warning_name: None,
        is_streamed: false,
    });

    de.print(&sm, false);

    let output_bytes = raw_buf.lock().unwrap();
    let output_str = String::from_utf8_lossy(&output_bytes);
    assert!(
        output_str.contains("Test custom note"),
        "Output should contain the custom note, got: {}",
        output_str
    );
}
