use crate::driver::artifact::{CompilePhase, PipelineOutputs};
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;

pub(crate) fn setup_driver(source: &str, phase: CompilePhase) -> CompilerDriver {
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    CompilerDriver::from_config(config)
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
