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
fn test_printf_long_double() {
    let code = r#"
#include <stdio.h>
int main() {
    printf("%.1Lf", 34.1L);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "34.1");
}

#[test]
fn test_printf_mixed_long_double() {
    let code = r#"
#include <stdio.h>
int main() {
    printf("%f %.1Lf %d", 1.0, 34.1L, 42);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.000000 34.1 42");
}

#[test]
fn test_myprintf_repro() {
    // Original reproduction case
    let code = r#"
#include <stdarg.h>
#include <stdio.h>

void myprintf(int count, ...) {
    va_list ap;
    va_start(ap, count);
    for (int i = 0; i < count; i++) {
        long double x = va_arg(ap, long double);
        printf("%.1Lf ", x);
    }
    va_end(ap);
    printf("\n");
}

int main() {
    myprintf(1, 34.1L);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "34.1");
}
