#[cfg(test)]
mod tests {
    use cendol::parser::parser::Parser;
    use cendol::preprocessor::preprocessor::Preprocessor;
    use cendol::codegen::codegen::CodeGen;

    #[test]
    fn test_codegen() {
        let input = "1 + 2 * 3";
        let mut preprocessor = Preprocessor::new();
        let tokens = preprocessor.preprocess(input).unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.expr().unwrap();
        let mut codegen = CodeGen::new();
        let code = codegen.compile(ast).unwrap();
        let code_fn = unsafe { std::mem::transmute::<_, fn(i64) -> i64>(code) };
        assert_eq!(code_fn(0), 7);
    }
}
