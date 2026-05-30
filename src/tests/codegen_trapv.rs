use std::process::Command;
use tempfile::NamedTempFile;

fn compile_and_run_c_with_ftrapv(source: &str, ftrapv: bool) -> std::process::Output {
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

    use crate::lang_options::SignedOverflowMode;
    config.lang_options.signed_overflow_mode = if ftrapv {
        SignedOverflowMode::Trap
    } else {
        SignedOverflowMode::Wrap
    };

    // Add include paths manually
    config
        .preprocessor
        .system_include_paths
        .push(std::path::PathBuf::from("custom-include"));

    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let result = driver.run();

    if result.is_err() || driver.sm.get_file_id("test.c").is_none() {
        driver.print_diagnostics();
        panic!("Compilation failed");
    }

    Command::new(exe_path).output().expect("Failed to execute")
}

#[test]
fn test_trapv_addition() {
    let source = r#"
        int main() {
            volatile int a = 2147483647;
            volatile int b = 1;
            volatile int c = a + b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}

#[test]
fn test_trapv_subtraction() {
    let source = r#"
        int main() {
            volatile int a = -2147483648;
            volatile int b = 1;
            volatile int c = a - b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}

#[test]
fn test_trapv_multiplication() {
    let source = r#"
        int main() {
            volatile int a = 1073741824;
            volatile int b = 2;
            volatile int c = a * b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}
