//! Common utilities for semantic analysis tests.
use crate::ast::Ast;
use crate::driver::artifact::CompilePhase;
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::semantic::TypeRegistry;
use crate::tests::test_utils;

pub fn run_pass(source: &str, phase: CompilePhase) {
    let (driver, result) = test_utils::run_pipeline(source, phase);
    if result.is_err() {
        panic!("Compilation failed unexpectedly: {:?}", driver.get_diagnostics());
    }
}

pub fn run_fail(source: &str, phase: CompilePhase) -> CompilerDriver {
    let (driver, result) = test_utils::run_pipeline(source, phase);
    assert!(result.is_err(), "Compilation should have failed");
    driver
}

pub fn run_fail_with_message(source: &str, phase: CompilePhase, message: &str) {
    let driver = run_fail(source, phase);
    check_diagnostic_message_only(&driver, message);
}

pub fn run_fail_with_diagnostic(source: &str, phase: CompilePhase, message: &str, line: u32, col: u32) {
    let driver = run_fail(source, phase);
    check_diagnostic(&driver, message, line, col);
}

pub fn setup_mir(source: &str) -> String {
    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::Mir);
    let mut out = match result {
        Ok(out) => out,
        Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
    };
    let first = out.units.values_mut().next().expect("No units in output");
    let artifact = first;

    let sema_output = artifact.sema_output.as_ref().expect("No semantic output available");

    let dump_config = MirDumpConfig { include_header: false };
    let dumper = MirDumper::new(sema_output, &dump_config);

    dumper.generate_mir_dump().expect("Failed to generate MIR dump")
}

pub fn setup_lowering(source: &str) -> (Ast, TypeRegistry) {
    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SymbolResolver);
    let out = match result {
        Ok(out) => out,
        Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
    };
    let unit = out.units.into_iter().next().expect("No units in output").1;

    (
        unit.ast.expect("No AST available"),
        unit.type_registry.expect("No TypeRegistry available"),
    )
}

pub fn setup_diagnostics_output(source: &str) -> String {
    let (driver, _) = test_utils::run_pipeline(source, CompilePhase::Mir);
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

pub fn check_diagnostic(driver: &CompilerDriver, message: &str, line: u32, col: u32) {
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

pub fn check_diagnostic_message_only(driver: &CompilerDriver, message: &str) {
    let diagnostics = driver.get_diagnostics();
    let found = diagnostics.iter().any(|d| d.message.contains(message));
    assert!(
        found,
        "Expected diagnostic message containing '{}' not found.\nActual diagnostics: {:?}",
        message, diagnostics
    );
}

pub fn run_full_pass(source: &str) {
    let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::EmitObject);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run();
    if let Err(e) = result {
        panic!(
            "Driver run failed: {:?}. Diagnostics: {:?}",
            e,
            driver.get_diagnostics()
        );
    }
}
