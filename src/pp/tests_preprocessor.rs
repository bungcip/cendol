use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::intern::StringId;
use crate::source_manager::SourceManager;

/// Helper function to set up preprocessor testing
fn setup_preprocessor_test(src: &str) -> Vec<PPToken> {
    setup_preprocessor_test_with_diagnostics(src).unwrap().0
}

/// Helper function to set up preprocessor testing and return diagnostics
fn setup_preprocessor_test_with_diagnostics(
    src: &str,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    // Initialize logging for tests
    let _ = env_logger::try_init();

    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig {
        max_include_depth: 100,
        ..Default::default()
    };

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>");

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);

    let tokens = preprocessor.process(source_id, &config)?;

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    Ok((significant_tokens, diagnostics.diagnostics().to_vec()))
}

/// Helper macro to assert token sequence kinds
macro_rules! assert_token_kinds {
    ($tokens:expr, $( $expected:expr ),* $(,)?) => {{
        let expected_kinds = vec![$($expected),*];
        assert_eq!($tokens.len(), expected_kinds.len(), "Token count mismatch");
        for (i, (token, expected)) in $tokens.iter().zip(expected_kinds.iter()).enumerate() {
            assert_eq!(token.kind, *expected, "Token {} kind mismatch: expected {:?}, got {:?}", i, expected, token.kind);
        }
    }};
}

#[test]
fn test_simple_macro_definition_and_expansion() {
    let src = r#"
#define TEN 10
int x = TEN;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected kinds: Identifier("int"), Identifier("x"), Assign, Number("10"), Semicolon
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("10")),
        PPTokenKind::Semicolon
    );

    // Ensure TEN was not present (it should have been expanded)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "TEN", "TEN should have been expanded");
        }
    }
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    let src = r#"
#define ADD(a,b) ( (a) + (b) )
int x = ADD(3, 4);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, (, (, 3, ), +, (, 4, ), ), ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::LeftParen,
        PPTokenKind::LeftParen,
        PPTokenKind::Number(StringId::new("3")),
        PPTokenKind::RightParen,
        PPTokenKind::Plus,
        PPTokenKind::LeftParen,
        PPTokenKind::Number(StringId::new("4")),
        PPTokenKind::RightParen,
        PPTokenKind::RightParen,
        PPTokenKind::Semicolon
    );

    // Ensure ADD was not present (it should have been expanded)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "ADD", "ADD should have been expanded");
        }
    }
}

#[test]
fn test_variadic_macro_and_stringification() {
    let src = r#"
#define LOG(fmt, ...) printf(fmt, __VA_ARGS__)
#define STR(x) #x
const char* s = STR(hello_world);
LOG("value=%d\n", 5);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: const, char*, s, =, "hello_world", ;, printf, (, "value=%d\n", ,, 5, ), ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("const")),
        PPTokenKind::Identifier(StringId::new("char")),
        PPTokenKind::Star,
        PPTokenKind::Identifier(StringId::new("s")),
        PPTokenKind::Assign,
        PPTokenKind::StringLiteral(StringId::new("\"hello_world\"")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("printf")),
        PPTokenKind::LeftParen,
        PPTokenKind::StringLiteral(StringId::new("\"value=%d\\n\"")),
        PPTokenKind::Comma,
        PPTokenKind::Number(StringId::new("5")),
        PPTokenKind::RightParen,
        PPTokenKind::Semicolon
    );

    // Ensure macros were expanded
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            let name = sym.as_str();
            assert_ne!(name, "LOG", "LOG should have been expanded");
            assert_ne!(name, "STR", "STR should have been expanded");
            assert_ne!(name, "__VA_ARGS__", "__VA_ARGS__ should have been expanded");
        }
    }
}

#[test]
fn test_nested_ifdef_ifndef_and_defined_operator() {
    let src = r#"
#define A 1
#if defined(A)
#ifdef B
int x = 2;
#else
int x = 1;
#endif
#else
int x = 0;
#endif
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 1, ;
    // Since A is defined and B is not defined, it should take the #else branch
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );

    // Ensure A was not expanded (it's used in conditional)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "A", "A should not appear in output");
        }
    }
}

#[test]
fn test_arithmetic_in_if_expression_and_elif() {
    let src = r#"
#define VAL 8
#if VAL > 10
  int x = 100;
#elif VAL >= 8
  int x = 8;
#else
  int x = 0;
#endif
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 8, ;
    // Since VAL is 8, VAL > 10 is false, VAL >= 8 is true
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("8")),
        PPTokenKind::Semicolon
    );

    // Ensure VAL was expanded in the conditional but not in output
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "VAL", "VAL should not appear in output");
        }
    }
}

#[test]
fn test_macro_redefinition_warning_or_override() {
    let src = r#"
#define X 1
#define X 2
int x = X;
"#;

    let (significant_tokens, diagnostics) = setup_preprocessor_test_with_diagnostics(src).unwrap();

    // Expected: int, x, =, 2, ;
    // Since X is redefined from 1 to 2, the final value should be 2
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("2")),
        PPTokenKind::Semicolon
    );

    // Ensure X was expanded to the final definition
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "X", "X should not appear in output");
        }
    }

    // Check that a macro redefinition warning was emitted
    assert_eq!(diagnostics.len(), 1, "Should have exactly one diagnostic");
    assert_eq!(diagnostics[0].level, crate::diagnostic::DiagnosticLevel::Warning);
    assert!(diagnostics[0].message.contains("Redefinition of macro 'X'"));
    assert_eq!(diagnostics[0].code, Some("macro_redefinition".to_string()));
}

#[test]
fn test_predefined_macros_present() {
    let src = r#"
const int a = __STDC__;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: const, int, a, =, 1, ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("const")),
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("a")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );

    // Ensure __STDC__ was expanded
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "__STDC__", "__STDC__ should have been expanded");
        }
    }
}

#[test]
fn test_error_directive_produces_failure() {
    let src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;

    // This should fail due to #error directive
    let result = setup_preprocessor_test_with_diagnostics(src);
    assert!(result.is_err(), "Preprocessor should fail on #error directive");

    if let Err(PPError::ErrorDirective(message)) = result {
        assert_eq!(message, "\"this should be reported\"");
    } else {
        panic!("Expected ErrorDirective error");
    }
}

#[test]
fn test_complex_macro_expansion_and_recursion_limit() {
    let src = r#"
#define ID(x) x
#define A ID(ID(ID(1)))
int x = A;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 1, ;
    // A should expand to ID(ID(ID(1))) -> ID(ID(1)) -> ID(1) -> 1
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );

    // Ensure all macros were expanded
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            let name = sym.as_str();
            assert_ne!(name, "ID", "ID should have been expanded");
            assert_ne!(name, "A", "A should have been expanded");
        }
    }
}

#[test]
fn test_token_pasting() {
    let src = r#"
#define PASTE(a,b) a ## b
int foobar = 1;
int x = PASTE(foo, bar);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, foobar, =, 1, ;, int, x, =, foobar, ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("foobar")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Identifier(StringId::new("foobar")),
        PPTokenKind::Semicolon
    );

    // Ensure PASTE was expanded
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "PASTE", "PASTE should have been expanded");
        }
    }
}

#[test]
fn test_ifndef_conditional() {
    let src = r#"
#ifndef DEF
int x = 0;
#endif

#define DEF

#ifndef DEF
X;
#endif
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 0, ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("0")),
        PPTokenKind::Semicolon
    );

    // Ensure X was not included (since DEF is defined)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "X", "X should not appear in output");
        }
    }
}

#[test]
fn test_complex_arithmetic_expressions() {
    let src = r#"
// Test various arithmetic operations in preprocessor conditionals
#if (-2) != -2
#error fail
#endif

#if (0 || 0) != 0
#error fail
#endif

#if (1 || 0) != 1
#error fail
#endif

#if (0xf0 | 1) != 0xf1
#error fail
#endif

#if (1 << 1) != 2
#error fail
#endif

#if (2 + 1) != 3
#error fail
#endif

#if (2+2*3+2) != 10
#error fail
#endif

#if ((2+2)*(3+2)) != 20
#error fail
#endif

int result = 42;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, result, =, 42, ;
    // All conditionals should evaluate to false, so no #error should trigger
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("result")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("42")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_pragma_operator_removes_tokens() {
    let src = r#"
_Pragma("STDC FP_CONTRACT ON")
int x = 1;
"#;
    let significant_tokens = setup_preprocessor_test(src);

    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_pragma_once_via_pragma_operator() {
    let mut sm = SourceManager::new();
    let header_content = r#"
_Pragma("once")
int a = 1;
"#;
    sm.add_buffer(header_content.as_bytes().to_vec(), "header.h");

    let main_content = r#"
#include "header.h"
#include "header.h"
"#;
    let main_id = sm.add_buffer(main_content.as_bytes().to_vec(), "main.c");

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig::default();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);

    let tokens = pp.process(main_id, &config).unwrap();
    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    // The tokens from "header.h" should only appear once.
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("a")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_include_same_file_twice_without_pragma_once() {
    let mut sm = SourceManager::new();
    let header_content = "int a = 1;";
    sm.add_buffer(header_content.as_bytes().to_vec(), "header.h");

    let main_content = r#"
#include "header.h"
#include "header.h"
"#;
    let main_id = sm.add_buffer(main_content.as_bytes().to_vec(), "main.c");

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig::default();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);

    let tokens = pp.process(main_id, &config).unwrap();
    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    // The tokens from "header.h" should appear twice.
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("a")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("a")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_circular_include_in_memory() {
    let mut sm = SourceManager::new();
    sm.add_buffer("#include \"b.h\"".as_bytes().to_vec(), "a.h");
    sm.add_buffer("#include \"a.h\"".as_bytes().to_vec(), "b.h");
    let main_id = sm.add_buffer("#include \"a.h\"".as_bytes().to_vec(), "main.c");

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig {
        max_include_depth: 10,
        ..Default::default()
    };
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let result = pp.process(main_id, &config);

    assert!(matches!(result, Err(PPError::CircularInclude)));
}

#[test]
fn test_circular_include_error_with_temp_files() {
    let dir = tempfile::tempdir().unwrap();
    let path_a = dir.path().join("a.h");
    let path_b = dir.path().join("b.h");
    let path_main = dir.path().join("main.c");

    std::fs::write(&path_a, "#include \"b.h\"").unwrap();
    std::fs::write(&path_b, "#include \"a.h\"").unwrap();
    std::fs::write(&path_main, "#include \"a.h\"").unwrap();

    let mut sm = SourceManager::new();
    let source_id_main = sm.add_file_from_path(&path_main).unwrap();

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig {
        max_include_depth: 10,
        ..Default::default()
    };
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let result = pp.process(source_id_main, &config);

    assert!(matches!(result, Err(PPError::CircularInclude)));
}

#[test]
fn test_function_like_macro_not_expanded_when_not_followed_by_paren() {
    let src = r#"
#define x(y) ((y) + 1)
int x = x(0);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, (, (, 0, ), +, 1, ), ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::LeftParen,
        PPTokenKind::LeftParen,
        PPTokenKind::Number(StringId::new("0")),
        PPTokenKind::RightParen,
        PPTokenKind::Plus,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::RightParen,
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_object_macro_with_parentheses_in_replacement() {
    let src = r#"
#define NULL ((void*)0)
int x = NULL;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, (, void, *, ), 0, ), ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::LeftParen,
        PPTokenKind::Identifier(StringId::new("void")),
        PPTokenKind::Star,
        PPTokenKind::RightParen,
        PPTokenKind::Number(StringId::new("0")),
        PPTokenKind::RightParen,
        PPTokenKind::Semicolon
    );

    // Ensure NULL was expanded
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "NULL", "NULL should have been expanded");
        }
    }
}

#[test]
fn test_line_directive_presumed_location() {
    let src = r#"
// This is line 2
#line 100 "mapped.c"
// This is now logical line 101
int x = 1;
// This is logical line 102
int y = 2;
"#;

    let (significant_tokens, diagnostics) = setup_preprocessor_test_with_diagnostics(src).unwrap();

    // Expected tokens: int, x, =, 1, ;, int, y, =, 2, ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("y")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("2")),
        PPTokenKind::Semicolon
    );

    // No diagnostics expected
    assert_eq!(diagnostics.len(), 0);
}

#[test]
fn test_line_directive_with_diagnostics() {
    let src = r#"
#line 50 "test.c"
invalid syntax here
"#;

    let result = setup_preprocessor_test_with_diagnostics(src);

    // This should succeed at preprocessor level (we're not testing parsing here)
    // but the test demonstrates that line directives are processed
    assert!(result.is_ok());
}

#[test]
fn test_invalid_line_directive() {
    let src = r#"
#line invalid
int x = 1;
"#;

    let result = setup_preprocessor_test_with_diagnostics(src);
    assert!(result.is_err());

    if let Err(PPError::InvalidLineDirective) = result {
        // Expected error
    } else {
        panic!("Expected InvalidLineDirective error");
    }
}

#[test]
fn test_line_directive_zero_line_number() {
    let src = r#"
#line 0
int x = 1;
"#;

    let result = setup_preprocessor_test_with_diagnostics(src);
    assert!(result.is_err());

    if let Err(PPError::InvalidLineDirective) = result {
        // Expected error
    } else {
        panic!("Expected InvalidLineDirective error");
    }
}

#[test]
fn test_line_directive_malformed_filename() {
    let src = r#"
#line 100 invalid_filename
int x = 1;
"#;

    let result = setup_preprocessor_test_with_diagnostics(src);
    assert!(result.is_err());

    if let Err(PPError::InvalidLineDirective) = result {
        // Expected error
    } else {
        panic!("Expected InvalidLineDirective error");
    }
}

#[test]
fn test_multiline_macro_definition_only() {
    let src = r#"
#define EMPTY(X)  \
  X               \
  X
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Should produce no output since macro is defined but not used
    assert_eq!(significant_tokens.len(), 0);
}

#[test]
fn test_token_pasting_with_empty_argument() {
    let src = r#"
#define P(A,B) A ## B
int x = P(foo,);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Identifier(StringId::new("foo")),
        PPTokenKind::Semicolon
    );
}
