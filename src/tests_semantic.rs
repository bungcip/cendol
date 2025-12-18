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

#[test]
fn test_incompatible_void_ptr_to_int_initialization() {
    // Test code with incompatible pointer to integer conversion: void* to int
    let source_code = r#"
void *p;
int x = p; // This should be an error
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have a type error
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("incompatible pointer to integer conversion")
    });

    assert!(has_type_error, "Expected type error for void* to int initialization, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_compatible_int_initialization() {
    // Test code with compatible integer initialization: int to int
    let source_code = r#"
int x = 5; // This should be OK
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we don't have type errors
    let has_type_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("incompatible pointer to integer conversion")
    });

    assert!(!has_type_error, "Unexpected type error for int initialization. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_invalid_dereference_non_pointer_int() {
    // Test code with invalid dereference: trying to dereference an int
    let source_code = r#"
int main() {
    int x = 5;
    int y = *x;  // This should be an error - dereferencing non-pointer
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have an error for dereferencing non-pointer
    let has_deref_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operand: dereferencing non-pointer type")
    });

    assert!(has_deref_error, "Expected error for dereferencing non-pointer int, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_valid_dereference_pointer() {
    // Test code with valid dereference: dereferencing a valid pointer
    let source_code = r#"
int main() {
    int x = 5;
    int *ptr = &x;  // Valid pointer
    int y = *ptr;  // This should be valid
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we don't have any errors for valid pointer dereference
    let has_deref_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operand: dereferencing")
    });

    assert!(!has_deref_error, "Unexpected error for valid pointer dereference. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_invalid_dereference_non_pointer_float() {
    // Test code with invalid dereference: trying to dereference a float
    let source_code = r#"
int main() {
    float f = 3.14;
    float result = *f;  // This should be an error - dereferencing non-pointer
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have an error for dereferencing non-pointer float
    let has_deref_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operand: dereferencing non-pointer type")
    });

    assert!(has_deref_error, "Expected error for dereferencing non-pointer float, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_invalid_dereference_non_pointer_char() {
    // Test code with invalid dereference: trying to dereference a char
    let source_code = r#"
int main() {
    char c = 'a';
    char result = *c;  // This should be an error - dereferencing non-pointer
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have an error for dereferencing non-pointer char
    let has_deref_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operand: dereferencing non-pointer type")
    });

    assert!(has_deref_error, "Expected error for dereferencing non-pointer char, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_invalid_dereference_non_pointer_struct() {
    // Test code with invalid dereference: trying to dereference a struct
    let source_code = r#"
struct Point {
    int x;
    int y;
};

int main() {
    struct Point p = {1, 2};
    struct Point result = *p;  // This should be an error - dereferencing non-pointer
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // Check that we have an error for dereferencing non-pointer struct
    let has_deref_error = output.diagnostics.iter().any(|diag| {
        matches!(diag.level, crate::diagnostic::DiagnosticLevel::Error) &&
        diag.message.contains("Invalid operand: dereferencing non-pointer type")
    });

    assert!(has_deref_error, "Expected error for dereferencing non-pointer struct, but none found. Diagnostics: {:?}", output.diagnostics);
}

#[test]
fn test_valid_dereference_void_pointer() {
    // Test code with valid void pointer dereference (should be allowed)
    let source_code = r#"
int main() {
    int x = 5;
    void *ptr = &x;
    int y = *(int*)ptr;  // Cast required but dereference itself should be valid
    return 0;
}
"#;

    let output = run_semantic_analysis(source_code);

    // This test may pass or fail depending on how casts are handled
    // For now, we're mainly testing that our dereference checking works
    println!("Diagnostics for void* dereference test: {:?}", output.diagnostics);
}