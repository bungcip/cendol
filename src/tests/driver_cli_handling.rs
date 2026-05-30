use crate::driver::CompilerDriver;
use crate::driver::artifact::CompilePhase;
use crate::driver::cli::{CompileConfig, PathOrBuffer};
use crate::pp::PPToken;
use std::path::PathBuf;

fn compile_with_defines(source: &str, defines: &[(&str, Option<&str>)]) -> Vec<PPToken> {
    let mut config = CompileConfig::default();
    config
        .input_files
        .push(PathOrBuffer::Buffer("test.c".to_string(), source.as_bytes().to_vec()));
    for (name, val) in defines {
        config.defines.push((name.to_string(), val.map(|v| v.to_string())));
    }
    config.stop_after = CompilePhase::Preprocess;

    let mut driver = CompilerDriver::from_config(config);
    let outputs = driver
        .run_pipeline(CompilePhase::Preprocess)
        .expect("Compilation failed");

    let artifact = outputs.units.values().next().expect("No unit output");
    artifact.preprocessed.clone().expect("No tokens")
}

#[test]
fn test_driver_defines() {
    let source = r#"
#ifdef TEST_DEFINE
    int main(void) { return 42; }
#endif
"#;

    let tokens = compile_with_defines(source, &[("TEST_DEFINE", None)]);
    let has_main = tokens.iter().any(|t| t.get_text() == "main");
    assert!(has_main, "Output should contain 'main' when TEST_DEFINE is set");
}

#[test]
fn test_driver_defines_with_value() {
    let source = r#"
int main(void) { return SUCCESS; }
"#;

    let tokens = compile_with_defines(source, &[("SUCCESS", Some("ok"))]);
    let has_value = tokens.iter().any(|t| t.get_text() == "ok");
    assert!(has_value, "Output should contain 'ok' when SUCCESS is set to ok");
}

#[test]
fn test_external_object_handling() {
    let mut config = CompileConfig::default();
    let obj_path = PathBuf::from("test.o");
    config.input_files.push(PathOrBuffer::Path(obj_path.clone()));

    let mut driver = CompilerDriver::from_config(config);
    // Using CompilePhase::Parse to ensure we stop early, but for external object handling
    // it shouldn't matter as it bypasses the pipeline loop.
    let outputs = driver.run_pipeline(CompilePhase::Parse).expect("Pipeline failed");

    assert_eq!(outputs.external_object_files.len(), 1);
    let expected_path = std::fs::canonicalize(&obj_path).unwrap_or(obj_path);
    assert_eq!(outputs.external_object_files[0], expected_path);
    assert!(outputs.units.is_empty());
}
