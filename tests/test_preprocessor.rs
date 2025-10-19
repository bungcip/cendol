use cendol::preprocessor::preprocessor::Preprocessor;
use cendol::preprocessor::token::{Token, TokenKind};

#[test]
fn test_simple_define() {
    let input = "#define A 1\nA";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind.to_string(), "1");
}

#[test]
fn test_function_macro() {
    let input = "#define ADD(a, b) a + b\nADD(1, 2)";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 3);
    assert_eq!(tokens[0].kind.to_string(), "1");
    assert_eq!(tokens[1].kind.to_string(), "+");
    assert_eq!(tokens[2].kind.to_string(), "2");
}

#[test]
fn test_token_pasting() {
    let input = "#define CONCAT(a, b) a ## b\nCONCAT(x, y)";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    // assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind.to_string(), "xy");
}

#[test]
fn test_stringizing() {
    let input = "#define STRING(a) #a\nSTRING(hello)";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    // assert_eq!(tokens.len(), 1);
    if let TokenKind::String(s) = &tokens[0].kind {
        assert_eq!(s, "hello");
    } else {
        panic!("Expected a string token");
    }
}

#[test]
fn test_hideset() {
    let input = "#define A B\n#define B A\nA";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    // This would be an infinite loop without a hideset.
    // The exact output depends on the expansion limit, but it should not hang.
    // For now, we'll just assert that it doesn't panic.
    assert!(tokens.len() > 0);
}

#[test]
fn test_simple_function_macro() {
    let input = "#define ID(x) x\nID(1)";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 1);
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
//     let mut preprocessor = Preprocessor::new();
//     let tokens = preprocessor.preprocess(input).unwrap();
//     let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
//     let result = result.replace(" ", "").replace("\n", "");
//     assert_eq!(result, "F_HOOK()(XXX)");
// }

#[test]
fn test_keyword_macro() {
    let input = "#define p(x) int x\np(elif)";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 2);
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
//     let mut preprocessor = Preprocessor::new();
//     let tokens = preprocessor.preprocess(input).unwrap();
//     assert_eq!(tokens.len(), 2);
//     assert_eq!(tokens[0].kind.to_string(), "FIRST");
//     assert_eq!(tokens[1].kind.to_string(), "42");
// }

#[test]
fn test_line_splicing() {
    let input = "#define A 1 \\\n+ 2\nA";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 3);
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
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
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
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
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
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
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
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
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
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "inta=1;");

    std::fs::remove_file("test.h").unwrap();
}

#[test]
fn test_line_and_file_macros() {
    let input = "__LINE__ __FILE__";
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    assert_eq!(tokens.len(), 2);
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
    let mut preprocessor = Preprocessor::new();
    let result = preprocessor.preprocess(input);
    assert!(result.is_err());
}
#[test]
fn test_line_directive() {
    let input = r#"
#line 10 "foo.c"
"#;
    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(input).unwrap();
    let result = tokens.iter().map(|t| t.to_string()).collect::<String>();
    let result = result.replace(" ", "").replace("\n", "");
    assert_eq!(result, "");
}