#[cfg(test)]
mod tests {
    use cendol::codegen::CodeGen;
    use cendol::parser::Parser;
    use cendol::preprocessor::Preprocessor;
    use std::fs;
    use std::io::Write;
    use std::process::Command;

    #[test]
    fn test_codegen() {
        let input = "int main() { return 0; }";
        let mut preprocessor = Preprocessor::new();
        let tokens = preprocessor.preprocess(input).unwrap();
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
        let status = Command::new("cc")
            .arg("-c")
            .arg("tests/external.c")
            .arg("-o")
            .arg("tests/external.o")
            .status()
            .unwrap();
        assert!(status.success());

        let input = "int main() { return external_function(2, 3); }";
        let mut preprocessor = Preprocessor::new();
        let tokens = preprocessor.preprocess(input).unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.parse().unwrap();
        let codegen = CodeGen::new();
        let object_bytes = codegen.compile(ast).unwrap();

        let mut object_file = fs::File::create("test.o").unwrap();
        object_file.write_all(&object_bytes).unwrap();

        let status = Command::new("cc")
            .arg("test.o")
            .arg("tests/external.o")
            .arg("-o")
            .arg("test.out")
            .status()
            .unwrap();
        assert!(status.success());

        let output = Command::new("./test.out").status().unwrap();
        assert_eq!(output.code(), Some(5));
    }
}
