//! tests_compound_assign.rs - End-to-end tests for compound assignment operators.
//!
//! This module contains tests that compile and run C code with compound assignment
//! operators to verify their correctness in the generated executable.

use std::process::Command;
use tempfile::NamedTempFile;

fn run_c_code(source: &str) -> i32 {
    let temp_file = NamedTempFile::new().unwrap();
    let temp_path = temp_file.into_temp_path();
    let exe_path = temp_path.to_path_buf();

    let config = crate::driver::cli::CompileConfig {
        input_files: vec![crate::driver::cli::PathOrBuffer::Buffer(
            "test.c".into(),
            source.as_bytes().to_vec(),
        )],
        output_path: Some(exe_path.clone()),
        ..Default::default()
    };

    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let result = driver.run();

    // Check for compilation errors
    if result.is_err() || driver.source_manager.get_file_id("test.c").is_none() {
        driver.print_diagnostics();
        panic!("Compilation failed");
    }

    let run_output = Command::new(exe_path).output().expect("Failed to execute");

    run_output.status.code().unwrap_or(-1)
}

#[test]
fn test_compound_add_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x += 3; return x; }");
    assert_eq!(exit_code, 8, "Expected exit code 8 for x += 3");
}

#[test]
fn test_compound_sub_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x -= 3; return x; }");
    assert_eq!(exit_code, 2, "Expected exit code 2 for x -= 3");
}

#[test]
fn test_compound_mul_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x *= 3; return x; }");
    assert_eq!(exit_code, 15, "Expected exit code 15 for x *= 3");
}

#[test]
fn test_compound_div_assign() {
    let exit_code = run_c_code("int main() { int x = 10; x /= 2; return x; }");
    assert_eq!(exit_code, 5, "Expected exit code 5 for x /= 2");
}

#[test]
fn test_compound_mod_assign() {
    let exit_code = run_c_code("int main() { int x = 10; x %= 3; return x; }");
    assert_eq!(exit_code, 1, "Expected exit code 1 for x %= 3");
}

#[test]
fn test_compound_mixed_types() {
    let exit_code = run_c_code(
        r#"
        int main() {
            short s = 10;
            long l = 3;
            s -= l;
            return s;
        }
    "#,
    );
    assert_eq!(exit_code, 7, "Expected exit code 7 for short -= long");
}

#[test]
fn test_compound_unsigned_mixed_types() {
    let exit_code = run_c_code(
        r#"
        int main() {
            unsigned char c = 5;
            int i = 2;
            c += i;
            return c;
        }
    "#,
    );
    assert_eq!(exit_code, 7, "Expected exit code 7 for unsigned char += int");
}
