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

        let filename = "test_codegen_c.o";
        let exefile = format!("./{}", filename.replace(".o", ".out"));
        let mut object_file = fs::File::create(filename).unwrap();
        object_file.write_all(&object_bytes).unwrap();
        drop(object_file); // Explicitly close the file

        let status = Command::new("cc")
            .arg(filename)
            .arg("-o")
            .arg(&exefile)
            .arg("-lc") // Link against the C standard library
            .status()
            .unwrap();
        assert!(status.success());

        let output = Command::new(exefile).status().unwrap();
        assert_eq!(output.code(), Some(0));
    }
    #[test]
    fn test_external_function_call() {
        let input = r#"
        int puts(const char *s);
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

        let filename = "test_external_function_call_c.o";
        let exefile = format!("./{}", filename.replace(".o", ".out"));
        let mut object_file = fs::File::create(filename).unwrap();
        object_file.write_all(&object_bytes).unwrap();
        drop(object_file); // Explicitly close the file

        let status = Command::new("cc")
            .arg(filename)
            .arg("-o")
            .arg(&exefile)
            .arg("-lc") // Link against the C standard library
            .status()
            .unwrap();
        assert!(status.success());

        let output = Command::new(exefile).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "hello world\n");
    }
}
