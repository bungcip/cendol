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
