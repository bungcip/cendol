use crate::driver::CompilerDriver;
use crate::driver::artifact::CompilePhase;
use crate::driver::cli::{CompileConfig, PathOrBuffer};

#[test]
fn test_driver_defines() {
    let source = r#"
#ifdef TEST_DEFINE
    int main(void) { return 42; }
#endif
"#;

    let mut config = CompileConfig::default();
    config
        .input_files
        .push(PathOrBuffer::Buffer("test.c".to_string(), source.as_bytes().to_vec()));
    config.defines.push(("TEST_DEFINE".to_string(), None));
    config.stop_after = CompilePhase::Preprocess; // Just preprocess

    let mut driver = CompilerDriver::from_config(config);
    let outputs = driver
        .run_pipeline(CompilePhase::Preprocess)
        .expect("Compilation failed");

    // Check if output contains "main"
    let artifact = outputs.units.values().next().expect("No unit output");
    let tokens = artifact.preprocessed.as_ref().expect("No tokens");

    // Check tokens for "main"
    let has_main = tokens.iter().any(|t| t.get_text() == "main");
    assert!(has_main, "Output should contain 'main' when TEST_DEFINE is set");
}

#[test]
fn test_driver_defines_with_value() {
    let source = r#"
int main(void) { return VALUE; }
"#;

    let mut config = CompileConfig::default();
    config
        .input_files
        .push(PathOrBuffer::Buffer("test.c".to_string(), source.as_bytes().to_vec()));
    config.defines.push(("VALUE".to_string(), Some("123".to_string())));
    config.stop_after = CompilePhase::Preprocess;

    let mut driver = CompilerDriver::from_config(config);
    let outputs = driver
        .run_pipeline(CompilePhase::Preprocess)
        .expect("Compilation failed");

    let artifact = outputs.units.values().next().expect("No unit output");
    let tokens = artifact.preprocessed.as_ref().expect("No tokens");

    // Check tokens for "123"
    let has_value = tokens.iter().any(|t| t.get_text() == "123");
    assert!(has_value, "Output should contain '123' when VALUE is set to 123");
}
