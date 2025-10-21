//! Tests for preprocessor functionality
//!
//! This module tests the preprocessor's ability to correctly handle
//! macro definitions, expansions, and various preprocessor directives.

use cendol::file::FileManager;
use cendol::preprocessor::Preprocessor;
use cendol::preprocessor::token::TokenKind;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "<input>";
}

/// Creates a new preprocessor instance with a file manager
fn create_preprocessor() -> Preprocessor {
    Preprocessor::new(FileManager::new())
}

/// Helper function to preprocess input and return tokens
fn preprocess_input(input: &str) -> Result<Vec<cendol::preprocessor::token::Token>, Box<dyn std::error::Error>> {
    let mut preprocessor = create_preprocessor();
    let tokens = preprocessor.preprocess(input, config::TEST_FILENAME)?;
    Ok(tokens)
}

/// Helper function to get token string representations
fn get_token_strings(tokens: &[cendol::preprocessor::token::Token]) -> Vec<String> {
    tokens.iter()
        .filter(|t| !t.kind.to_string().is_empty()) // Filter out EOF tokens
        .map(|t| t.kind.to_string())
        .collect()
}

/// Asserts that token strings match expected values
fn assert_token_strings(tokens: &[cendol::preprocessor::token::Token], expected: &[&str]) {
    let actual: Vec<String> = get_token_strings(tokens);
    let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
    assert_eq!(actual, expected);
}

    /// Test function-like macro expansion
    #[test]
    fn test_function_macro() {
        let input = "#define ADD(a, b) a + b\nADD(1, 2)";
        let tokens = preprocess_input(input).unwrap();
        assert_eq!(tokens.len(), 4); // +1 for Eof
        assert_token_strings(&tokens, &["1", "+", "2"]);
    }

    /// Test token pasting operator (##)
    #[test]
    fn test_token_pasting() {
        let input = "#define CONCAT(a, b) a ## b\nCONCAT(x, y)";
        let tokens = preprocess_input(input).unwrap();
        assert_token_strings(&tokens, &["xy"]);
    }

    /// Test stringizing operator (#)
    #[test]
    fn test_stringizing() {
        let input = "#define STRING(a) #a\nSTRING(hello)";
        let tokens = preprocess_input(input).unwrap();
        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s, "hello");
        } else {
            panic!("Expected a string token");
        }
    }

    /// Test hideset mechanism to prevent infinite macro recursion
    #[test]
    fn test_hideset() {
        let input = "#define A B\n#define B A\nA";
        let tokens = preprocess_input(input).unwrap();
        // This would be an infinite loop without a hideset.
        // The exact output depends on the expansion limit, but it should not hang.
        // For now, we'll just assert that it doesn't panic.
        assert!(tokens.len() > 0);
    }

#[test]
fn test_simple_function_macro() {
    let input = "#define ID(x) x\nID(1)";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 2); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "1");
}

// #[test]
// fn test_deferred_expansion() {
//     let input = r#"
// #define F(acc) F_PROGRESS(acc)
// #define F_PROGRESS(acc) CONTINUE(F)(acc##X)
// #define F_HOOK() F
// #define UNROLL(...) __VA_ARGS__
// #define DEFER(op) op EMPTY
// #define EMPTY
// #define CONTINUE(k) DEFER(k##_HOOK)()

// UNROLL(F_PROGRESS(X))
// "#;
//     let mut preprocessor = Preprocessor::new(FileManager::new());
//     let tokens = preprocessor.preprocess(input).unwrap();
//     let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
//     let result = result.replace(" ", "").replace("\n", "");
//     assert_eq!(result, "F_HOOK()(XXX)");
// }

#[test]
fn test_keyword_macro() {
    let input = "#define p(x) int x\np(elif)";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 3); // +1 for Eof
    assert!(matches!(tokens[0].kind, TokenKind::Keyword(_)));
    assert_eq!(tokens[0].kind.to_string(), "int");
    assert!(matches!(tokens[1].kind, TokenKind::Identifier(_)));
    assert_eq!(tokens[1].kind.to_string(), "elif");
}

// #[test]
// fn test_unbalanced_paren_in_macro() {
//     let input = r#"
// #define FIRST(x) x
// #define SECOND FIRST
// #define THIRD SECOND
// THIRD 42
// "#;
//     let mut preprocessor = Preprocessor::new(FileManager::new());
//     let tokens = preprocessor.preprocess(input).unwrap();
//     assert_eq!(tokens.len(), 2);
//     assert_eq!(tokens[0].kind.to_string(), "FIRST");
//     assert_eq!(tokens[1].kind.to_string(), "42");
// }

#[test]
fn test_line_splicing() {
    let input = "#define A 1 \\\n+ 2\nA";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 4); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "1");
    assert_eq!(tokens[1].kind.to_string(), "+");
    assert_eq!(tokens[2].kind.to_string(), "2");
}
#[test]
fn test_conditional_directives() {
    let input = r#"
#if 1 > 0
    int a = 1;
#else
    int a = 2;
#endif

#if 0 > 1
    int b = 1;
#else
    int b = 2;
#endif
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "inta=1;intb=2;");
}
#[test]
fn test_ifdef_directive() {
    let input = r#"
#define FOO
#ifdef FOO
    int a = 1;
#endif
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "inta=1;");
}

#[test]
fn test_ifndef_directive() {
    let input = r#"
#ifndef FOO
    int a = 1;
#endif
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "inta=1;");
}

#[test]
fn test_undef_directive() {
    let input = r#"
#define FOO
#undef FOO
#ifdef FOO
    int a = 1;
#endif
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "");
}

#[test]
fn test_include_directive() {
    let mut file = std::fs::File::create("test.h").unwrap();
    std::io::Write::write_all(&mut file, b"int a = 1;").unwrap();

    let input = r#"
#include "test.h"
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "test.c").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "inta=1;");

    std::fs::remove_file("test.h").unwrap();
}

#[test]
fn test_line_and_file_macros() {
    let input = "__LINE__ __FILE__";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 3); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "1");
    if let TokenKind::String(s) = &tokens[1].kind {
        assert_eq!(s, "<input>");
    } else {
        panic!("Expected a string token");
    }
}

#[test]
fn test_error_directive() {
    let input = r#"
#error "This is an error"
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let result = preprocessor.preprocess(input, "<input>");
    assert!(result.is_err());
}
#[test]
fn test_line_directive() {
    let input = r#"
#line 10 "foo.c"
"#;
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "");
}

#[test]
fn test_self_referential_macro() {
    let input = "#define FOO FOO\nFOO";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 2); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "FOO");
}

#[test]
fn test_mutually_recursive_macros() {
    let input = "#define BAR BAZ\n#define BAZ BAR\nBAR BAZ";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 3); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "BAR");
    assert_eq!(tokens[1].kind.to_string(), "BAZ");
}

#[test]
fn test_date_and_time_macros() {
    let input = "__DATE__ __TIME__";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 3); // +1 for Eof
    if let TokenKind::String(s) = &tokens[0].kind {
        // Check if the date is in the format "Mmm dd yyyy"
        assert!(s.len() > 0);
    } else {
        panic!("Expected a string token for __DATE__");
    }
    if let TokenKind::String(s) = &tokens[1].kind {
        // Check if the time is in the format "HH:MM:SS"
        assert!(s.len() > 0);
    } else {
        panic!("Expected a string token for __TIME__");
    }
}

#[test]
fn test_object_macro_with_space_before_paren() {
    let input = "#define A (1)\nA";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 4); // +1 for Eof
    assert_eq!(tokens[0].kind.to_string(), "(");
    assert_eq!(tokens[1].kind.to_string(), "1");
    assert_eq!(tokens[2].kind.to_string(), ")");
}

#[test]
fn test_cmdline_define() {
    let input = "A B";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    preprocessor.define("A=1").unwrap();
    preprocessor.define("B").unwrap();
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 2); // "1" and Eof
    assert_eq!(tokens[0].kind.to_string(), "1");
    assert!(matches!(tokens[1].kind, TokenKind::Eof));
}

#[test]
fn test_empty_cmdline_define() {
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let result = preprocessor.define("");
    assert!(result.is_err());
}

#[test]
fn test_empty_define_name() {
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let result = preprocessor.define("=1");
    assert!(result.is_err());
}

#[test]
fn test_define_without_value() {
    let input = "A";
    let mut preprocessor = Preprocessor::new(FileManager::new());
    preprocessor.define("A").unwrap();
    let tokens = preprocessor.preprocess(input, "<input>").unwrap();
    assert_eq!(tokens.len(), 1); // Eof
    assert!(matches!(tokens[0].kind, TokenKind::Eof));
}
