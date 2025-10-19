#[cfg(test)]
mod tests {
    use cendol::parser::ast::{Expr, Function, Program, Stmt};
    use cendol::parser::parser::Parser;
    use cendol::preprocessor::preprocessor::Preprocessor;

    #[test]
    fn test_parser() {
        let input = "int main() { return 0; }";
        let mut preprocessor = Preprocessor::new();
        let tokens = preprocessor.preprocess(input).unwrap();
        let mut parser = Parser::new(tokens).unwrap();
        let ast = parser.parse().unwrap();
        assert_eq!(
            ast,
            Program {
                function: Function {
                    name: "main".to_string(),
                    body: Stmt::Return(Expr::Number(0))
                }
            }
        );
    }
}
