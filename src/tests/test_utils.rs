use crate::diagnostic::DiagnosticEngine;
use crate::driver::artifact::{CompilePhase, PipelineOutputs};
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;
use crate::source_manager::SourceManager;

pub(crate) fn setup_driver(source: &str, phase: CompilePhase) -> CompilerDriver {
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    CompilerDriver::from_config(config)
}

pub(crate) fn setup_sm_and_diag() -> (SourceManager, DiagnosticEngine) {
    let source_manager = SourceManager::new();
    let diagnostics = DiagnosticEngine::default();
    (source_manager, diagnostics)
}

pub(crate) fn run_pipeline(source: &str, phase: CompilePhase) -> (CompilerDriver, Result<PipelineOutputs, String>) {
    let mut driver = setup_driver(source, phase);
    let result = driver.run_pipeline(phase).map_err(|e| format!("{:?}", e));
    (driver, result)
}

pub(crate) fn run_pipeline_to_mir(source: &str) -> PipelineOutputs {
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    if let Err(e) = &result {
        driver.print_diagnostics();
        panic!("Pipeline failed: {}", e);
    }
    result.unwrap()
}

pub(crate) fn sort_clif_ir(ir: &str) -> String {
    let chunks: Vec<&str> = ir.split("\n\n").collect();
    let mut functions = Vec::new();
    let mut current_function = String::new();

    for chunk in chunks {
        if chunk.trim().is_empty() {
            continue;
        }

        if chunk.trim_start().starts_with("; Function:") {
            if !current_function.is_empty() {
                functions.push(current_function);
            }
            current_function = chunk.trim_start().to_string();
        } else if !current_function.is_empty() {
            current_function.push_str("\n\n");
            current_function.push_str(chunk);
        } else {
            current_function = chunk.to_string();
        }
    }
    if !current_function.is_empty() {
        functions.push(current_function);
    }

    functions.sort();
    functions.join("\n\n")
}

pub(crate) fn run_pass(source: &str, phase: CompilePhase) {
    let (driver, result) = run_pipeline(source, phase);
    if result.is_err() {
        panic!("Compilation failed unexpectedly: {:?}", driver.get_diagnostics());
    }
}

pub(crate) fn run_fail(source: &str, phase: CompilePhase) -> CompilerDriver {
    let (driver, result) = run_pipeline(source, phase);
    assert!(result.is_err(), "Compilation should have failed");
    driver
}

pub(crate) fn run_fail_with_message(source: &str, message: &str) {
    let driver = run_fail(source, CompilePhase::Mir);
    check_diagnostic_message_only(&driver, message);
}

pub(crate) fn run_fail_with_diagnostic(source: &str, phase: CompilePhase, message: &str, line: u32, col: u32) {
    let driver = run_fail(source, phase);
    check_diagnostic(&driver, message, line, col);
}

pub(crate) fn check_diagnostic(driver: &CompilerDriver, message: &str, line: u32, col: u32) {
    let diagnostics = driver.get_diagnostics();
    let found = diagnostics.iter().any(|d| {
        if d.message.contains(message)
            && let Some((l, c)) = driver.source_manager.get_line_column(d.span.start())
            && l == line
            && c == col
        {
            return true;
        }
        false
    });
    assert!(
        found,
        "Expected diagnostic message containing '{}' at {}:{} not found.\nActual diagnostics: {:?}",
        message, line, col, diagnostics
    );
}

pub(crate) fn check_diagnostic_message_only(driver: &CompilerDriver, message: &str) {
    let diagnostics = driver.get_diagnostics();
    let found = diagnostics.iter().any(|d| d.message.contains(message));
    assert!(
        found,
        "Expected diagnostic message containing '{}' not found.\nActual diagnostics: {:?}",
        message, diagnostics
    );
}

pub(crate) fn setup_diagnostics_output(source: &str) -> String {
    let (driver, _) = run_pipeline(source, CompilePhase::Mir);
    let diagnostics = driver.get_diagnostics();

    format!(
        "Diagnostics count: {}\n\n{}",
        diagnostics.len(),
        diagnostics
            .iter()
            .map(|diag| format!(
                "Level: {:?}\nMessage: {}\nSpan: {}",
                diag.level, diag.message, diag.span
            ))
            .collect::<Vec<_>>()
            .join("\n\n")
    )
}

pub(crate) fn run_pass_with_diagnostic(source: &str, phase: CompilePhase, message: &str, line: u32, col: u32) {
    let (driver, result) = run_pipeline(source, phase);
    assert!(result.is_ok(), "Compilation should have succeeded");
    check_diagnostic(&driver, message, line, col);
}
