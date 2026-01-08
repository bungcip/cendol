use crate::driver::artifact::{CompilePhase, PipelineOutputs};
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;

pub fn setup_driver(source: &str, phase: CompilePhase) -> CompilerDriver {
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    CompilerDriver::from_config(config)
}

pub fn run_pipeline(source: &str, phase: CompilePhase) -> (CompilerDriver, Result<PipelineOutputs, String>) {
    let mut driver = setup_driver(source, phase);
    let result = driver.run_pipeline(phase).map_err(|e| format!("{:?}", e));
    (driver, result)
}

pub fn run_pipeline_success(source: &str, phase: CompilePhase) -> (CompilerDriver, PipelineOutputs) {
    let (driver, result) = run_pipeline(source, phase);
    match result {
        Ok(output) => (driver, output),
        Err(e) => {
            driver.print_diagnostics();
            panic!("Compilation failed: {}", e);
        }
    }
}
