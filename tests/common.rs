//! Shared test utilities for the cendol project
//!
//! This module provides common utilities and patterns used across different
//! test modules to reduce code duplication and improve maintainability.

use cendol::codegen::CodeGen;
use cendol::common::{SourceLocation, SourceSpan};
use cendol::file::{FileId, FileManager};
use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt, Type};
use cendol::preprocessor::Preprocessor;
use cendol::preprocessor::lexer::Lexer;
use cendol::preprocessor::token::{KeywordKind, Token, TokenKind};
use std::fs;
use std::io::Write;
use std::process::Command;

/// Test configuration constants
pub mod config {
    /// Default C compiler to use for linking generated code
    pub const C_COMPILER: &str = "cc";
    /// Standard C library flag for linking
    pub const C_LIB_FLAG: &str = "-lc";
    /// Default object file extension
    pub const OBJ_EXTENSION: &str = ".o";
    /// Default executable extension
    pub const EXE_EXTENSION: &str = ".out";
    /// Test file prefix for generated files
    pub const TEST_FILE_PREFIX: &str = "test_";
}

/// Creates a new preprocessor instance with a file manager
pub fn create_preprocessor() -> Preprocessor {
    Preprocessor::new(FileManager::new())
}

/// Creates a new file manager instance
pub fn create_file_manager() -> FileManager {
    FileManager::new()
}

/// Creates a source location for testing
pub fn create_test_location(file_id: u32, line: u32) -> SourceSpan {
    let location = SourceLocation::new(FileId(file_id), line, 1);
    SourceSpan::new(FileId(file_id), location.clone(), location)
}

/// Compiles C code through the full pipeline (preprocessor -> parser -> codegen)
pub fn compile_to_object_bytes(
    input: &str,
    filename: &str,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut preprocessor = create_preprocessor();
    let tokens = preprocessor.preprocess(input, filename)?;

    // Parser now handles filtering internally
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast)?;
    Ok(object_bytes)
}

/// Compiles and runs C code, returning the exit code
pub fn compile_and_run(input: &str, test_name: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut preprocessor = create_preprocessor();
    let tokens = preprocessor.preprocess(input, &format!("{}.c", test_name))?;

    // Parser now handles filtering internally
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast)?;

    let obj_filename = format!(
        "{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::OBJ_EXTENSION
    );
    let exe_filename = format!(
        "./{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::EXE_EXTENSION
    );

    // Write object file
    let mut object_file = fs::File::create(&obj_filename)?;
    object_file.write_all(&object_bytes)?;
    drop(object_file); // Explicitly close the file

    // Compile object file to executable
    let compile_status = Command::new(config::C_COMPILER)
        .arg(&obj_filename)
        .arg("-o")
        .arg(&exe_filename)
        .arg(config::C_LIB_FLAG)
        .status()?;

    if !compile_status.success() {
        return Err(format!("Compilation failed for test: {}", test_name).into());
    }

    // Run executable and get exit code
    let output = Command::new(&exe_filename).status()?;
    let exit_code = output.code().unwrap_or(-1);

    // Clean up generated files
    let _ = fs::remove_file(&obj_filename);
    let _ = fs::remove_file(&exe_filename);

    Ok(exit_code)
}

/// Compiles and runs C code, capturing stdout output
pub fn compile_and_run_with_output(
    input: &str,
    test_name: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut preprocessor = create_preprocessor();
    let tokens = preprocessor.preprocess(input, &format!("{}.c", test_name))?;

    // Parser now handles filtering internally
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast)?;

    let obj_filename = format!(
        "{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::OBJ_EXTENSION
    );
    let exe_filename = format!(
        "./{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::EXE_EXTENSION
    );

    // Write object file
    let mut object_file = fs::File::create(&obj_filename)?;
    object_file.write_all(&object_bytes)?;
    drop(object_file);

    // Compile object file to executable
    let compile_status = Command::new(config::C_COMPILER)
        .arg(&obj_filename)
        .arg("-o")
        .arg(&exe_filename)
        .arg(config::C_LIB_FLAG)
        .status()?;

    if !compile_status.success() {
        return Err(format!("Compilation failed for test: {}", test_name).into());
    }

    // Run executable and capture output
    let output = Command::new(&exe_filename).output()?;
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();

    // Clean up generated files
    let _ = fs::remove_file(&obj_filename);
    let _ = fs::remove_file(&exe_filename);

    Ok(stdout)
}

/// Creates a vector of tokens for manual testing
pub fn create_test_tokens() -> Vec<Token> {
    let mut file_manager = create_file_manager();
    let file_id = file_manager.open("test.c").unwrap();
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

/// Creates a simple C program AST for testing
pub fn create_simple_program_ast() -> Program {
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


/// Helper function to collect all tokens from a lexer
pub fn collect_tokens_from_lexer(input: &str, filename: &str) -> Vec<Token> {
    let mut file_manager = create_file_manager();
    let file_id = file_manager.open(filename).unwrap();
    let mut lexer = Lexer::new(input, file_id);
    let mut tokens = Vec::new();

    loop {
        let token = lexer.next_token().unwrap();
        if let TokenKind::Eof = token.kind {
            break;
        }
        tokens.push(token);
    }

    tokens
}

/// Helper function to extract token kinds from tokens
pub fn get_token_kinds(tokens: &[Token]) -> Vec<TokenKind> {
    tokens.iter().map(|t| t.kind.clone()).collect()
}

/// Asserts that two token kind vectors are equal
pub fn assert_tokens_equal(actual: &[Token], expected: &[TokenKind]) {
    let actual_kinds: Vec<TokenKind> = actual.iter().map(|t| t.kind.clone()).collect();
    assert_eq!(actual_kinds, expected.to_vec());
}

/// Asserts that two AST programs are equal
pub fn assert_programs_equal(actual: &Program, expected: &Program) {
    assert_eq!(actual.globals.len(), expected.globals.len());
    assert_eq!(actual.functions.len(), expected.functions.len());
    assert_eq!(actual.functions[0].name, expected.functions[0].name);
    assert_eq!(
        actual.functions[0].params.len(),
        expected.functions[0].params.len()
    );
    assert_eq!(
        actual.functions[0].body.len(),
        expected.functions[0].body.len()
    );
}

/// Cleanup helper for generated test files
pub fn cleanup_test_files(test_name: &str) {
    let obj_filename = format!(
        "{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::OBJ_EXTENSION
    );
    let exe_filename = format!(
        "./{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::EXE_EXTENSION
    );

    let _ = fs::remove_file(&obj_filename);
    let _ = fs::remove_file(&exe_filename);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_simple_program_ast() {
        let ast = create_simple_program_ast();
        assert_eq!(ast.functions[0].name, "main");
        assert_eq!(ast.functions[0].body.len(), 1);
        if let Stmt::Return(_) = &ast.functions[0].body[0] {
            // Expected return statement
        } else {
            panic!("Expected return statement");
        }
    }

    #[test]
    fn test_collect_tokens_from_lexer() {
        let input = "int main";
        let tokens = collect_tokens_from_lexer(input, "test.c");
        assert_eq!(tokens.len(), 3);
        assert!(matches!(
            tokens[0].kind,
            TokenKind::Keyword(KeywordKind::Int)
        ));
        assert!(matches!(tokens[1].kind, TokenKind::Whitespace(_)));
        assert!(matches!(tokens[2].kind, TokenKind::Identifier(_)));
    }

    #[test]
    fn test_get_token_kinds() {
        let tokens = vec![
            Token {
                kind: TokenKind::Keyword(KeywordKind::Int),
                span: create_test_location(0, 0),
                hideset: std::collections::HashSet::new(),
                expansion_locs: Vec::new(),
            },
            Token {
                kind: TokenKind::Identifier("main".to_string()),
                span: create_test_location(0, 0),
                hideset: std::collections::HashSet::new(),
                expansion_locs: Vec::new(),
            },
        ];
        let kinds = get_token_kinds(&tokens);
        assert_eq!(kinds.len(), 2);
        assert!(matches!(kinds[0], TokenKind::Keyword(KeywordKind::Int)));
        assert!(matches!(kinds[1], TokenKind::Identifier(_)));
    }
}

use cendol::error::Report;

/// Compiles C code and returns a report on error
pub fn compile_and_get_error(input: &str, filename: &str) -> Result<(), Report> {
    let mut preprocessor = create_preprocessor();
    let tokens = match preprocessor.preprocess(input, filename) {
        Ok(tokens) => tokens,
        Err(err) => return Err(Report::new(err.to_string(), None, None)),
    };

    // Parser now handles filtering internally

    let mut parser = match Parser::new(tokens) {
        Ok(parser) => parser,
        Err(err) => {
            return Err(Report::new(
                err.to_string(),
                Some(filename.to_string()),
                None,
            ));
        }
    };
    match parser.parse() {
        Ok(_) => Ok(()),
        Err(err) => {
            let (msg, location) = match err {
                cendol::parser::error::ParserError::UnexpectedToken(tok) => {
                    ("Unexpected token".to_string(), Some(tok.span))
                }
                cendol::parser::error::ParserError::UnexpectedEof => {
                    ("Unexpected EOF".to_string(), None)
                }
            };

            let (path, span) = if let Some(location) = location {
                let path = preprocessor
                    .file_manager()
                    .get_path(location.start.file)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                (Some(path), Some(location))
            } else {
                (Some(filename.to_string()), None)
            };

            Err(Report::new(msg, path, span))
        }
    }
}
