#[cfg(test)]
mod tests {
    use cendol::parser::parser::Parser;
    use cendol::preprocessor::preprocessor::Preprocessor;
    use cendol::parser::ast::Expr;

    #[test]
    fn test_parser() {
        let input = "1 + 2 * 3";
        let mut preprocessor = Preprocessor::new();
        let tokens = preprocessor.preprocess(input).unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.expr().unwrap();
        assert_eq!(
            ast,
            Expr::Add(
                Box::new(Expr::Number(1)),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2)),
                    Box::new(Expr::Number(3))
                ))
            )
        );
    }
}
