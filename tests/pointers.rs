#[cfg(test)]
mod tests {

    // #[test]
    // fn test_pointers() {
    //     let input = "int main() { int x; int *p; p = &x; *p = 42; return x; }";
    //     let mut preprocessor = Preprocessor::new();
    //     let tokens = preprocessor.preprocess(input).unwrap();
    //     let mut parser = Parser::new(tokens).unwrap();
    //     let ast = parser.parse().unwrap();
    //     let codegen = CodeGen::new();
    //     let object_bytes = codegen.compile(ast).unwrap();

    //     let mut object_file = fs::File::create("test.o").unwrap();
    //     object_file.write_all(&object_bytes).unwrap();

    //     let status = Command::new("cc")
    //         .arg("test.o")
    //         .arg("-o")
    //         .arg("test.out")
    //         .status()
    //         .unwrap();
    //     assert!(status.success());

    //     let output = Command::new("./test.out").status().unwrap();
    //     assert_eq!(output.code(), Some(42));
    // }
}
