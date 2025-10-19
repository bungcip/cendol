#[cfg(test)]
mod tests {
    use cendol::codegen::codegen::CodeGen;
    use cendol::parser::parser::Parser;
    use cendol::preprocessor::preprocessor::Preprocessor;
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
}
