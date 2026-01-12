use std::process::Command;
use tempfile::NamedTempFile;

fn run_c_code(source: &str) -> Result<i32, String> {
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

    if result.is_err() {
        return Err("Compilation failed".into());
    }

    let run_output = Command::new(exe_path).output().expect("Failed to execute");
    Ok(run_output.status.code().unwrap_or(-1))
}

#[test]
fn test_pointer_add_assign() {
    let code = r#"
int main() {
    int arr[2];
    int *p = &arr[0];
    p += 1;
    if (p == &arr[1]) return 0;
    return 1;
}
"#;
    let result = run_c_code(code);
    assert!(result.is_ok(), "Pointer add-assign should compile and run");
    assert_eq!(result.unwrap(), 0, "Pointer should point to the second element");
}

#[test]
fn test_pointer_sub_assign() {
    let code = r#"
int main() {
    int arr[2];
    int *p = &arr[1];
    p -= 1;
    if (p == &arr[0]) return 0;
    return 1;
}
"#;
    let result = run_c_code(code);
    assert!(result.is_ok(), "Pointer sub-assign should compile and run");
    assert_eq!(result.unwrap(), 0, "Pointer should point to the first element");
}
