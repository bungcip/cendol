use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lexer::{Lexer, Token};
use crate::parser::Parser;
use crate::pp::{PPConfig, Preprocessor};
use crate::semantic::SemanticAnalyzer;
use crate::source_manager::SourceManager;
use crate::lang_options::LangOptions;
use target_lexicon::Triple;

/// Helper function to run semantic analysis on source code
fn run_semantic_analysis(source_code: &str) -> crate::semantic::SemanticOutput {
    let mut source_manager = SourceManager::new();
    let source_id = source_manager.add_buffer(source_code.as_bytes().to_vec(), "test.c");

    // Preprocess
    let pp_config = PPConfig::default();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::host();
    let mut diag_pp = DiagnosticEngine::new();
    let mut preprocessor = Preprocessor::new(
        &mut source_manager,
        &mut diag_pp,
        lang_opts.clone(),
        target_info.clone(),
        &pp_config,
    );

    let pp_tokens = preprocessor.process(source_id, &pp_config).unwrap();

    // Tokenize
    let mut lexer = Lexer::new(&pp_tokens);
    let tokens: Vec<Token> = lexer.tokenize_all();

    // Parse
    let mut ast = Ast::new();
    let mut diag = DiagnosticEngine::new();
    let mut parser = Parser::new(&tokens, &mut ast, &mut diag);
    let root_node = parser.parse_translation_unit().unwrap();

    // Set root
    ast.set_root_node(root_node);

    // Run semantic analysis
    let mut analyzer = SemanticAnalyzer::new(&mut ast, &mut diag);
    analyzer.analyze()
}

#[test]
fn test_incompatible_type_addition() {
    // Test code with incompatible types: pointer + pointer
    let source_code = r#"
int main() {
    int x = 5;
    int y = 10;
    int *p1 = &x;
    int *p2 = &y;
    int result = p1 + p2;  // This should be an error
    return result;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have a type error
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operands to binary +")
    });

    assert!(has_type_error, "Expected type error for pointer + pointer, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_compatible_type_addition() {
    // Test code with compatible types: int + int
    let source_code = r#"
int main() {
    int x = 5;
    int y = 10;
    int result = x + y;  // This should be OK
    return result;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we don't have type errors
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operands")
    });

    assert!(!has_type_error, "Unexpected type error for int + int. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_incompatible_type_subtraction() {
    // Test code with incompatible pointer types: int* - double*
    let source_code = r#"
int main() {
    int x = 5;
    double y = 10.0;
    int *a = &x;
    double *b = &y;
    long d = a - b; // Should raise a type error
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have a type error
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operands to binary -: incompatible pointer types")
    });

    assert!(has_type_error, "Expected type error for incompatible pointer subtraction, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_compatible_pointer_subtraction() {
    // Test code with compatible pointer types: int* - int*
    let source_code = r#"
int main() {
    int x = 5;
    int y = 10;
    int *a = &x;
    int *b = &y;
    long d = a - b; // This should be OK
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we don't have type errors
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operands to binary -")
    });

    assert!(!has_type_error, "Unexpected type error for compatible pointer subtraction. Diagnostics: {:?}", output.diagnostics);
}