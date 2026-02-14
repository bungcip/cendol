use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;
use std::process::Command;
use tempfile::NamedTempFile;

/// setup test with output is cranelift ir
pub(crate) fn setup_cranelift(c_code: &str) -> String {
    let (driver, pipeline_result) = test_utils::run_pipeline(c_code, CompilePhase::Cranelift);
    match pipeline_result {
        Err(_) => {
            driver.print_diagnostics();
            panic!("Compilation failed");
        }
        Ok(outputs) => {
            let artifact = outputs.units.values().next().unwrap();
            let clif_dump = artifact.clif_dump.as_ref().unwrap();
            clif_dump.to_string()
        }
    }
}

fn compile_and_run_c(source: &str) -> std::process::Output {
    let temp_file = NamedTempFile::new().unwrap();
    let temp_path = temp_file.into_temp_path();
    let exe_path = temp_path.to_path_buf();

    let mut config = crate::driver::cli::CompileConfig {
        input_files: vec![crate::driver::cli::PathOrBuffer::Buffer(
            "test.c".into(),
            source.as_bytes().to_vec(),
        )],
        output_path: Some(exe_path.clone()),
        ..Default::default()
    };

    // Add include paths manually since we are not using CLI parsing
    config
        .preprocessor
        .system_include_paths
        .push(std::path::PathBuf::from("custom-include"));

    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let result = driver.run();

    // Check for compilation errors
    if result.is_err() || driver.source_manager.get_file_id("test.c").is_none() {
        driver.print_diagnostics();
        panic!("Compilation failed");
    }

    Command::new(exe_path).output().expect("Failed to execute")
}

pub(crate) fn run_c_code_with_output(source: &str) -> String {
    let run_output = compile_and_run_c(source);
    String::from_utf8_lossy(&run_output.stdout).to_string()
}

pub(crate) fn run_c_code_exit_status(source: &str) -> i32 {
    let run_output = compile_and_run_c(source);
    run_output.status.code().unwrap_or(-1)
}
