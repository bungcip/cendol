use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt};
use cendol::preprocessor::token::{KeywordKind, PunctKind, Token, TokenKind};
#[cfg(test)]
mod tests {
    use cendol::parser::Parser;
    use cendol::parser::ast::{Expr, Function, Program, Stmt};
    use cendol::preprocessor::Preprocessor;

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
                globals: vec![],
                function: Function {
                    name: "main".to_string(),
                    params: vec![],
                    body: vec![Stmt::Return(Expr::Number(0))]
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
        Token::new(TokenKind::Keyword(KeywordKind::Int), loc.clone()),
        Token::new(TokenKind::Whitespace(" ".to_string()), loc.clone()),
        Token::new(TokenKind::Identifier("main".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::LeftParen), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::RightParen), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::LeftBrace), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::If), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::LeftParen), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::RightParen), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::Semicolon), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Else), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("0".to_string()), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::Semicolon), loc.clone()),
        Token::new(TokenKind::Punct(PunctKind::RightBrace), loc.clone()),
    ];
    let mut parser = Parser::new(tokens).unwrap();
    let program = parser.parse().unwrap();
    assert_eq!(
        program,
        Program {
            globals: vec![],
            function: Function {
                name: "main".to_string(),
                params: vec![],
                body: vec![Stmt::If(
                    Box::new(Expr::Number(1)),
                    Box::new(Stmt::Return(Expr::Number(1))),
                    Some(Box::new(Stmt::Return(Expr::Number(0))))
                )]
            }
        }
    );
}
