use std::process::Command;
use tempfile::NamedTempFile;

fn run_c_code_with_output(source: &str) -> String {
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

    let run_output = Command::new(exe_path).output().expect("Failed to execute");
    String::from_utf8_lossy(&run_output.stdout).to_string()
}

#[test]
fn test_hfa_mixed_args() {
    let code = r#"
#include <stdio.h>

struct hfa_float2 { float a, b; } f2 = { 1.1f, 1.2f };
struct hfa_double1 { double a; } d1 = { 2.2 };
int i1 = 1;
int i2 = 2;

void mixed_args(int i1, struct hfa_float2 a, int i2, struct hfa_double1 c)
{
    printf("%d %.1f %.1f %d %.1f", i1, a.a, a.b, i2, c.a);
}

int main() {
    mixed_args(i1, f2, i2, d1);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1 1.1 1.2 2 2.2");
}
