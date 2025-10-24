//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::common::{SourceLocation, SourceSpan};
use cendol::file::FileManager;
use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt, Type};
use cendol::parser::token::{KeywordKind, Token, TokenKind};
use cendol::preprocessor::Preprocessor;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<Program, Box<dyn std::error::Error>> {
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
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::Return(Expr::Number(0))],
        }],
    }
}

/// Creates a program AST with a _Bool variable declaration
fn create_bool_program_ast() -> Program {
    Program {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![
                Stmt::Declaration(
                    Type::Bool,
                    "a".to_string(),
                    Some(Box::new(Expr::Number(1))),
                    false,
                ),
                Stmt::Return(Expr::Number(0)),
            ],
        }],
    }
}

/// Creates a program AST with variable declaration and increment
fn create_increment_program_ast() -> Program {
    Program {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![
                Stmt::Declaration(
                    Type::Int,
                    "a".to_string(),
                    Some(Box::new(Expr::Number(0))),
                    false,
                ),
                Stmt::Expr(Expr::Increment(Box::new(Expr::Variable(
                    "a".to_string(),
                    SourceSpan::new(
                        cendol::file::FileId(0),
                        SourceLocation::new(cendol::file::FileId(0), 1, 1),
                        SourceLocation::new(cendol::file::FileId(0), 1, 1),
                    ),
                )))),
                Stmt::Return(Expr::Number(0)),
            ],
        }],
    }
}

/// Creates a program AST with if-else control flow
fn create_control_flow_program_ast() -> Program {
    Program {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::If(
                Box::new(Expr::Number(1)),
                Box::new(Stmt::Return(Expr::Number(1))),
                Some(Box::new(Stmt::Return(Expr::Number(0)))),
            )],
        }],
    }
}

/// Creates a vector of tokens for manual testing
fn create_test_tokens() -> Vec<Token> {
    let mut file_manager = FileManager::new();
    let file_id = file_manager.open(config::TEST_FILENAME).unwrap();
    let location = SourceLocation::new(file_id, 0, 1);
    let loc = SourceSpan::new(file_id, location.clone(), location);

    vec![
        Token::new(TokenKind::Keyword(KeywordKind::Int), loc.clone()),
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
        Token::new(TokenKind::Eof, loc.clone()),
    ]
}

#[cfg(test)]
mod tests {
    use super::{
        create_bool_program_ast, create_control_flow_program_ast, create_increment_program_ast,
        create_simple_program_ast, parse_c_code,
    };
    use cendol::parser::ast::{Expr, Stmt, Type};

    /// Test parsing of simple C programs
    #[test]
    fn test_simple_program() {
        let input = "int main() { return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_simple_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(
            ast.functions[0].body.len(),
            expected.functions[0].body.len()
        );
    }

    /// Test parsing of programs with variable declarations and increment operations
    #[test]
    fn test_increment_program() {
        let input = "int main() { int a = 0; a++; return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_increment_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(
            ast.functions[0].body.len(),
            expected.functions[0].body.len()
        );
    }

    /// Test parsing of programs with control flow (if-else statements)
    #[test]
    fn test_control_flow() {
        let input = "int main() { if (1) return 1; else return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_control_flow_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(
            ast.functions[0].body.len(),
            expected.functions[0].body.len()
        );
    }

    /// Test parsing of programs with _Bool variable declarations
    #[test]
    fn test_bool_declaration() {
        let input = "int main() { _Bool a = 1; return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_bool_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(ast.functions[0].body, expected.functions[0].body);
    }

    /// Test parsing of designated initializers for structs
    #[test]
    fn test_designated_initializer() {
        let input =
            "int main() { struct { int x; int y; } point = { .y = 10, .x = 20 }; return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected_body = vec![
            Stmt::Declaration(
                Type::Struct(
                    None,
                    vec![
                        cendol::parser::ast::Parameter {
                            ty: Type::Int,
                            name: "x".to_string(),
                        },
                        cendol::parser::ast::Parameter {
                            ty: Type::Int,
                            name: "y".to_string(),
                        },
                    ],
                ),
                "point".to_string(),
                Some(Box::new(Expr::StructInitializer(vec![
                    Expr::DesignatedInitializer("y".to_string(), Box::new(Expr::Number(10))),
                    Expr::DesignatedInitializer("x".to_string(), Box::new(Expr::Number(20))),
                ]))),
                false,
            ),
            Stmt::Return(Expr::Number(0)),
        ];
        assert_eq!(ast.functions[0].body, expected_body);
    }
}
