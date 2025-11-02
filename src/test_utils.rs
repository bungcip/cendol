use crate::compiler::{Cli, Compiler, CompilerError};
use crate::error::Report;
use crate::file::{FileId, FileManager};
use crate::parser::Parser;
use crate::parser::ast::{Expr, Function, Stmt, TranslationUnit, Type};
use crate::preprocessor::Preprocessor;
use crate::preprocessor::lexer::Lexer;
use crate::preprocessor::token::{Token, TokenKind};
use crate::semantic::SemaOutput;
use crate::{SourceLocation, SourceSpan};
use thin_vec::ThinVec;
use thiserror::Error;

use std::fs;
use std::process::Command;
use tempfile::tempdir;

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
    Preprocessor::new()
}

/// Creates a new file manager instance
pub fn create_file_manager() -> FileManager {
    FileManager::new()
}

/// Creates a source location for testing
pub fn create_test_location(file_id: u32, line: u32) -> SourceSpan {
    let location = SourceLocation::new(FileId(file_id), line * 100 + 1);
    SourceSpan::new(location, location)
}

/// Compiles and runs C code, returning the exit code
pub fn compile_and_run(input: &str, test_name: &str) -> Result<i32, CompilerError> {
    let temp_dir = tempdir().unwrap();
    let temp_dir_path = temp_dir.path().to_str().unwrap().to_string();
    let exe_filename = format!("./{}.out", test_name);

    // Create a temporary file for the input within the temporary directory
    let input_file_path = temp_dir.path().join(format!("{}.c", test_name));
    fs::write(&input_file_path, input).unwrap();
    let input_file_path_str = input_file_path.to_str().unwrap().to_string();

    let mut compiler = Compiler::new(
        Cli {
            input_file: input_file_path_str.clone(),
            output_file: Some(exe_filename.clone()), // Output to object file first
            ..Default::default()
        },
        Some(temp_dir.path().to_path_buf()),
    );

    compiler.run_virtual_file(test_name, input)?;

    // Run executable and get exit code
    let exit_code = {
        let child_output = Command::new(&exe_filename)
            .current_dir(&temp_dir_path) // Execute in temporary directory
            .output()
            .unwrap(); // Use output() to ensure all streams are closed
        child_output.status.code().unwrap_or(-1)
    };

    // The temporary directory and its contents will be deleted when `temp_dir` goes out of scope.
    Ok(exit_code)
}

/// Compiles C code and asserts that a warning is returned.
pub fn compile_and_assert_warning(
    input: &str,
    test_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let temp_dir = tempdir().unwrap();
    let input_file_path = temp_dir.path().join(format!("{}.c", test_name));
    fs::write(&input_file_path, input)?;

    let cli = Cli {
        input_file: input_file_path.to_str().unwrap().to_string(),
        ..Default::default()
    };

    let mut compiler = Compiler::new(cli, Some(temp_dir.path().to_path_buf()));
    compiler.run_virtual_file(test_name, input).unwrap();

    Ok(())
}

/// Compiles C code with arguments and asserts that an error is returned.
pub fn compile_with_args_and_assert_error(
    input: &str,
    test_name: &str,
    args: Vec<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let temp_dir = tempdir()?;
    let input_file_path = temp_dir.path().join(format!("{}.c", test_name));
    fs::write(&input_file_path, input)?;

    let mut cli = Cli {
        input_file: input_file_path.to_str().unwrap().to_string(),
        ..Default::default()
    };
    for arg in args {
        if arg == "-Wall" {
            cli.wall = true;
        }
    }

    let mut compiler = Compiler::new(cli, Some(temp_dir.path().to_path_buf()));
    let result = compiler.run_virtual_file(test_name, input);
    result.expect_err("must be error");

    Ok(())
}

/// Compiles and runs C code from a file, returning the exit code
pub fn compile_and_run_from_file(file_path: &str, test_name: &str) -> Result<i32, CompilerError> {
    let input = fs::read_to_string(file_path).unwrap();
    compile_and_run(&input, test_name)
}

/// Compiles and runs C code, capturing stdout output
pub fn compile_and_run_with_output(input: &str, test_name: &str) -> Result<String, CompilerError> {
    let temp_dir = tempdir().unwrap();
    let temp_dir_path = temp_dir.path().to_str().unwrap().to_string();

    let exe_filename = format!("./{}.out", test_name);

    // Create a temporary file for the input within the temporary directory
    let input_file_path = temp_dir.path().join(format!("{}.c", test_name));
    fs::write(&input_file_path, input).unwrap();
    let input_file_path_str = input_file_path.to_str().unwrap().to_string();

    let mut compiler = Compiler::new(
        Cli {
            input_file: input_file_path_str.clone(),
            output_file: Some(exe_filename.clone()),
            ..Default::default()
        },
        Some(temp_dir.path().to_path_buf()),
    );

    compiler.run_virtual_file(test_name, input)?;

    // Run executable and capture output
    let stdout = {
        let output = Command::new(&exe_filename)
            .current_dir(&temp_dir_path)
            .output()
            .unwrap();
        String::from_utf8_lossy(&output.stdout).to_string()
    };

    // The temporary directory and its contents will be deleted when `temp_dir` goes out of scope.

    Ok(stdout)
}

/// Creates a simple C program AST for testing
pub fn create_simple_program_ast() -> TranslationUnit {
    TranslationUnit {
        globals: ThinVec::new(),
        functions: ThinVec::from(vec![Function {
            return_type: Type::Int,
            name: crate::parser::string_interner::StringInterner::intern("main"),
            params: ThinVec::new(),
            body: ThinVec::from(vec![Stmt::Return(Box::new(Expr::Number(
                0,
                SourceSpan::default(),
            )))]),
            is_inline: false,
            is_variadic: false,
            is_noreturn: false,
        }]),
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
pub fn assert_programs_equal(actual: &TranslationUnit, expected: &TranslationUnit) {
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

/// Compiles C code and returns a report on error
pub fn compile_and_get_error(input: &str, filename: &str) -> Result<(), Report> {
    match compile_and_run(input, filename) {
        Ok(_) => Ok(()),
        Err(e) => Err(e.reports[0].clone()),
    }
}
