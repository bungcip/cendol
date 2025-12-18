use super::*;
use crate::driver::CompilerDriver;
use crate::driver::cli::CompileConfig;

#[test]
fn test_compile_to_object_file() {
    let source = "int main() { return 2; }";
    let mut compiler = CompilerDriver::from_config(CompileConfig::from_source_code(source.to_string()));
    let ast = compiler.compile_to_ast().unwrap();
    let codegen = CodeGenerator::new(&ast);
    let object_file = codegen.compile().unwrap();
    let temp_dir = tempfile::tempdir().unwrap();
    let object_path = temp_dir.path().join("test.o");
    std::fs::write(&object_path, object_file).unwrap();
    let output_path = temp_dir.path().join("test");
    let output = std::process::Command::new("cc")
        .arg(&object_path)
        .arg("-o")
        .arg(&output_path)
        .output()
        .unwrap();
    assert!(output.status.success());
    let output = std::process::Command::new(output_path).output().unwrap();
    assert_eq!(output.status.code(), Some(2));
}

#[test]
fn test_codegen_with_semantic_lowering() {
    // Test that codegen works with semantic lowering enabled
    let source = "int main() { int x = 5; return x; }";
    let mut compiler = CompilerDriver::from_config(CompileConfig::from_source_code(source.to_string()));
    let ast = compiler.compile_to_ast().unwrap();
    let codegen = CodeGenerator::new(&ast);
    let result = codegen.compile();
    assert!(result.is_ok(), "Code generation should succeed with semantic lowering");
}

#[test]
fn test_codegen_with_variable_declaration() {
    // Test that variable declarations work correctly
    let source = "int main() { int x = 42; int y = 10; return x + y; }";
    let mut compiler = CompilerDriver::from_config(CompileConfig::from_source_code(source.to_string()));
    let ast = compiler.compile_to_ast().unwrap();
    let codegen = CodeGenerator::new(&ast);
    let result = codegen.compile();
    assert!(
        result.is_ok(),
        "Code generation should succeed with variable declarations"
    );
}
