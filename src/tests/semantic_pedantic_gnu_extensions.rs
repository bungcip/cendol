use crate::diagnostic::DiagnosticLevel;

#[test]
fn test_gnu_statement_expression_warning() {
    let source = r#"
        int main() {
            int x = ({ int y = 5; y; });
            return x;
        }
    "#;
    let mut config = crate::driver::cli::CompileConfig::from_virtual_file(
        source.to_string(),
        crate::driver::artifact::CompilePhase::SemanticLowering,
    );
    config.lang_options.pedantic = true;
    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let _ = driver.run_pipeline(crate::driver::artifact::CompilePhase::SemanticLowering);
    let diags = driver.get_diagnostics();
    assert!(diags.iter().any(|d| d.message.contains("use of GNU statement expression extension") && d.level == DiagnosticLevel::Warning));
}
