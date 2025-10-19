#[cfg(test)]
mod tests {
    use cendol::codegen::CodeGen;
    use cendol::file::FileManager;
    use cendol::parser::Parser;
    use cendol::preprocessor::Preprocessor;
    use std::fs;
    use std::io::Write;
    use std::process::Command;

    #[test]
    fn test_codegen() {
        let input = "int main() { return 0; }";
        let mut preprocessor = Preprocessor::new(FileManager::new());
        let tokens = preprocessor.preprocess(input, "test.c").unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.parse().unwrap();
        let codegen = CodeGen::new();
        let object_bytes = codegen.compile(ast).unwrap();

        let mut object_file = fs::File::create("test.o").unwrap();
        object_file.write_all(&object_bytes).unwrap();

        let status = Command::new("cc")
            .arg("test.o")
            .arg("-o")
            .arg("test.out")
            .status()
            .unwrap();
        assert!(status.success());

        let output = Command::new("./test.out").status().unwrap();
        assert_eq!(output.code(), Some(0));
    }
    #[test]
    fn test_external_function_call() {
        let input = r#"
        int main() {
            puts("hello world");
            return 0;
        }
        "#;
        let mut preprocessor = Preprocessor::new(FileManager::new());
        let tokens = preprocessor.preprocess(input, "test.c").unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.parse().unwrap();
        let codegen = CodeGen::new();
        let object_bytes = codegen.compile(ast).unwrap();

        let mut object_file = fs::File::create("test.o").unwrap();
        object_file.write_all(&object_bytes).unwrap();

        let status = Command::new("cc")
            .arg("test.o")
            .arg("-o")
            .arg("test.out")
            .status()
            .unwrap();
        assert!(status.success());

        let output = Command::new("./test.out").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "hello world\n");
    }
}
