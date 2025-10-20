//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt, Type};
use cendol::preprocessor::token::{KeywordKind, Token, TokenKind, SourceLocation};
use cendol::file::{FileManager, FileId};
use cendol::preprocessor::Preprocessor;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Creates a new preprocessor instance with a file manager
fn create_preprocessor() -> Preprocessor {
    Preprocessor::new(FileManager::new())
}

/// Creates a source location for testing
fn create_test_location(file_id: u32, line: u32) -> SourceLocation {
    SourceLocation { file: FileId(file_id), line }
}

/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<Program, Box<dyn std::error::Error>> {
    let mut preprocessor = create_preprocessor();
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
    let loc = create_test_location(file_id.0, 0);

    vec![
        Token::new(TokenKind::Keyword(KeywordKind::Int), loc.clone()),
        Token::new(TokenKind::Whitespace(" ".to_string()), loc.clone()),
        Token::new(TokenKind::Identifier("main".to_string()), loc.clone()),
        Token::new(TokenKind::LeftParen, loc.clone()),
        Token::new(TokenKind::RightParen, loc.clone()),
        Token::new(TokenKind::LeftBrace, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::If), loc.clone()),
        Token::new(TokenKind::LeftParen, loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::RightParen, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Semicolon, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Else), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("0".to_string()), loc.clone()),
        Token::new(TokenKind::Semicolon, loc.clone()),
        Token::new(TokenKind::RightBrace, loc.clone()),
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
        let tokens = create_test_tokens();
        let mut parser = Parser::new(tokens).unwrap();
        let program = parser.parse().unwrap();
        let expected = create_control_flow_program_ast();
        assert_eq!(program.function.name, expected.function.name);
        assert_eq!(program.function.body.len(), expected.function.body.len());
    }
}
fn test_control_flow() {
    let mut file_manager = FileManager::new();
    let file_id = file_manager.open("test.c").unwrap();
    let loc = SourceLocation {
        file: file_id,
        line: 0,
    };
    let tokens = vec![
        Token::new(TokenKind::Keyword(KeywordKind::Int), loc.clone()),
        Token::new(TokenKind::Whitespace(" ".to_string()), loc.clone()),
        Token::new(TokenKind::Identifier("main".to_string()), loc.clone()),
        Token::new(TokenKind::LeftParen, loc.clone()),
        Token::new(TokenKind::RightParen, loc.clone()),
        Token::new(TokenKind::LeftBrace, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::If), loc.clone()),
        Token::new(TokenKind::LeftParen, loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::RightParen, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("1".to_string()), loc.clone()),
        Token::new(TokenKind::Semicolon, loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Else), loc.clone()),
        Token::new(TokenKind::Keyword(KeywordKind::Return), loc.clone()),
        Token::new(TokenKind::Number("0".to_string()), loc.clone()),
        Token::new(TokenKind::Semicolon, loc.clone()),
        Token::new(TokenKind::RightBrace, loc.clone()),
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
