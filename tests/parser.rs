use cendol::parser::ast::{Expr, Function, Program, Stmt};
use cendol::parser::parser::Parser;
use cendol::preprocessor::token::{Token, TokenKind};
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
                    body: Box::new(Stmt::Return(Expr::Number(0)))
                }
            }
        );
    }
}

use cendol::preprocessor::token::SourceLocation;

#[test]
fn test_control_flow() {
    let loc = SourceLocation {
        file: "test".to_string(),
        line: 0,
    };
    let tokens = vec![
        Token::new(TokenKind::Keyword("int".to_string()), loc.clone()),
        Token::new(TokenKind::Whitespace(" ".to_string()), loc.clone()),
        Token::new(TokenKind::Identifier("main".to_string()), loc.clone()),
        Token::new(TokenKind::Punct("(".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(")".to_string()), loc.clone()),
        Token::new(TokenKind::Punct("{".to_string()), loc.clone()),
        Token::new(TokenKind::Keyword("if".to_string()), loc.clone()),
        Token::new(TokenKind::Punct("(".to_string()), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(")".to_string()), loc.clone()),
        Token::new(TokenKind::Keyword("return".to_string()), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(";".to_string()), loc.clone()),
        Token::new(TokenKind::Keyword("else".to_string()), loc.clone()),
        Token::new(TokenKind::Keyword("return".to_string()), loc.clone()),
        Token::new(TokenKind::Number("0".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(";".to_string()), loc.clone()),
        Token::new(TokenKind::Punct("}".to_string()), loc.clone()),
    ];
    let mut parser = Parser::new(tokens).unwrap();
    let program = parser.parse().unwrap();
    assert_eq!(
        program,
        Program {
            function: Function {
                name: "main".to_string(),
                body: Box::new(Stmt::If(
                    Box::new(Expr::Number(1)),
                    Box::new(Stmt::Return(Expr::Number(1))),
                    Some(Box::new(Stmt::Return(Expr::Number(0))))
                ))
            }
        }
    );
}
