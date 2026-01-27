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
fn test_printf_double() {
    let code = r#"
#include <stdio.h>
int main() {
    printf("%f", 1.25);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.250000");
}

#[test]
fn test_printf_multiple_doubles() {
    let code = r#"
#include <stdio.h>
int main() {
    printf("%f, %f", 1.25, 2.5);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.250000, 2.500000");
}

#[test]
fn test_printf_mixed_types() {
    let code = r#"
#include <stdio.h>
int main() {
    printf("int: %d, double: %f, str: %s", 42, 3.14159, "hello");
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "int: 42, double: 3.141590, str: hello");
}
