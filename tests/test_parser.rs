//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::common::{SourceLocation, SourceSpan};
use cendol::file::FileManager;
use cendol::logger::Logger;
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
    let logger = Logger::new(true); // Enable verbose logging for debugging
    let mut parser = Parser::new(tokens, logger)?;
    let ast = parser.parse()?;
    Ok(ast)
}

/// helper function to parse C function body and return the statements
fn parse_c_body(input: &str) -> Vec<Stmt> {
    let input = format!("
        int func1() {{ return 0; }}
        int func2(int a, int b, int c) {{ return 0; }}
        struct S {{ int member; }};

        void c_body(int x, int y, int a, int b, int c, int arr[], struct S obj, struct S *ptr, int *p)
        {{
            {input}
        }}
    ");

    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor
        .preprocess(&input, config::TEST_FILENAME)
        .unwrap();
    let logger = Logger::new(true); // Enable verbose logging for debugging
    let mut parser = Parser::new(tokens, logger).unwrap();
    let ast = parser.parse().unwrap();
    let body = ast.functions.last().unwrap().body.clone();
    body
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
            is_inline: false,
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
                Stmt::Declaration(Type::Bool, "a".to_string(), Some(Box::new(Expr::Number(1)))),
                Stmt::Return(Expr::Number(0)),
            ],
            is_inline: false,
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
                Stmt::Declaration(Type::Int, "a".to_string(), Some(Box::new(Expr::Number(0)))),
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
            is_inline: false,
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
            is_inline: false,
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
    use crate::parse_c_body;

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
            ),
            Stmt::Return(Expr::Number(0)),
        ];
        assert_eq!(ast.functions[0].body, expected_body);
    }

    #[test]
    fn test_all_expressions() {
        let input = r#"
            // Primary
            x;
            42;
            'a';
            "hello";
            (x + 1);

            // Postfix
            arr[2];
            func1();
            func2(a, b, c);
            obj.member;
            ptr->member;
            x++;
            y--;
            (int){1, 2}; // compound literal (C99)

            // unary
            ++x;
            --y;
            &x;
            *p;
            +x;
            -x;
            ~x;
            !x;
            sizeof x;
            sizeof(int);
        "#;
        let stmts = parse_c_body(input);

        // primary expressions
        assert!(matches!(stmts[0], Stmt::Expr(Expr::Variable(_, _))));
        assert!(matches!(stmts[1], Stmt::Expr(Expr::Number(_))));
        assert!(matches!(stmts[2], Stmt::Expr(Expr::Char(_))));
        assert!(matches!(stmts[3], Stmt::Expr(Expr::String(_))));
        assert!(matches!(stmts[4], Stmt::Expr(Expr::Add(..)))); // currenty don't have Paren expr

        // postfix expressions
        assert!(matches!(stmts[5], Stmt::Expr(Expr::Deref(..))));
        assert!(matches!(stmts[6], Stmt::Expr(Expr::Call(..))));
        assert!(matches!(stmts[7], Stmt::Expr(Expr::Call(..))));
        assert!(matches!(stmts[8], Stmt::Expr(Expr::Member(..))));
        assert!(matches!(stmts[9], Stmt::Expr(Expr::PointerMember(..))));
        assert!(matches!(stmts[10], Stmt::Expr(Expr::Increment(..))));
        assert!(matches!(stmts[11], Stmt::Expr(Expr::Decrement(..))));
        assert!(matches!(stmts[12], Stmt::Expr(Expr::CompoundLiteral(..))));

        // unary expressions continued
        assert!(matches!(stmts[21], Stmt::Expr(Expr::Sizeof(..))));
        assert!(matches!(stmts[22], Stmt::Expr(Expr::SizeofType(..))));

    }
}
