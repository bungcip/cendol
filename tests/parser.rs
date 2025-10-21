//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt, Type};
use cendol::parser::token::{Token, TokenKind, KeywordKind, PunctKind};
use cendol::file::{FileManager, FileId};
use cendol::preprocessor::token::SourceLocation;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}


/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<Program, Box<dyn std::error::Error>> {
    use cendol::preprocessor::Preprocessor;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, config::TEST_FILENAME)?;
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    Ok(ast)
}

/// Creates a simple C program AST for testing
fn create_simple_program_ast() -> Program {
    Program {
        globals: vec![],
        function: Function {
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::Return(Expr::Number(0))],
        },
    }
}

/// Creates a program AST with variable declaration and increment
fn create_increment_program_ast() -> Program {
    Program {
        globals: vec![],
        function: Function {
            name: "main".to_string(),
            params: vec![],
            body: vec![
                Stmt::Declaration(
                    Type::Int,
                    "a".to_string(),
                    Some(Box::new(Expr::Number(0))),
                ),
                Stmt::Expr(Expr::Increment(Box::new(Expr::Variable("a".to_string())))),
                Stmt::Return(Expr::Number(0)),
            ],
        },
    }
}

/// Creates a program AST with if-else control flow
fn create_control_flow_program_ast() -> Program {
    Program {
        globals: vec![],
        function: Function {
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::If(
                Box::new(Expr::Number(1)),
                Box::new(Stmt::Return(Expr::Number(1))),
                Some(Box::new(Stmt::Return(Expr::Number(0)))),
            )],
        },
    }
}

/// Creates a vector of tokens for manual testing
fn create_test_tokens() -> Vec<Token> {
    let mut file_manager = FileManager::new();
    let file_id = file_manager.open(config::TEST_FILENAME).unwrap();
    let loc = SourceLocation { file: file_id, line: 0 };

    vec![
        Token::new(TokenKind::Keyword(KeywordKind::Int), loc.clone()),
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
        Token::new(TokenKind::Eof, loc.clone()),
    ]
}

#[cfg(test)]
mod tests {
    use super::{parse_c_code, create_simple_program_ast, create_increment_program_ast, create_control_flow_program_ast, create_test_tokens, Parser};

    /// Test parsing of simple C programs
    #[test]
    fn test_simple_program() {
        let input = "int main() { return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_simple_program_ast();
        assert_eq!(ast.function.name, expected.function.name);
        assert_eq!(ast.function.body.len(), expected.function.body.len());
    }

    /// Test parsing of programs with variable declarations and increment operations
    #[test]
    fn test_increment_program() {
        let input = "int main() { int a = 0; a++; return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_increment_program_ast();
        assert_eq!(ast.function.name, expected.function.name);
        assert_eq!(ast.function.body.len(), expected.function.body.len());
    }

    /// Test parsing of programs with control flow (if-else statements)
    #[test]
    fn test_control_flow() {
        let input = "int main() { if (1) return 1; else return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_control_flow_program_ast();
        assert_eq!(ast.function.name, expected.function.name);
        assert_eq!(ast.function.body.len(), expected.function.body.len());
    }

}
