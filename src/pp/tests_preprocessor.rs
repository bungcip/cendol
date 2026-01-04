use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::source_manager::SourceManager;
use serde::Serialize;

#[derive(Serialize)]
struct DebugToken {
    kind: String,
    text: String,
}

impl From<&PPToken> for DebugToken {
    fn from(token: &PPToken) -> Self {
        let kind_str = match &token.kind {
            PPTokenKind::Identifier(_) => "Identifier".to_string(),
            PPTokenKind::StringLiteral(_) => "StringLiteral".to_string(),
            PPTokenKind::Number(_) => "Number".to_string(),
            PPTokenKind::CharLiteral(_, _) => "CharLiteral".to_string(),
            k => format!("{:?}", k),
        };

        DebugToken {
            kind: kind_str,
            text: token.get_text().to_string(),
        }
    }
}

fn setup_pp_snapshot(src: &str) -> Vec<DebugToken> {
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src).unwrap();
    tokens.iter().map(DebugToken::from).collect()
}

fn setup_pp_snapshot_with_diags(src: &str) -> (Vec<DebugToken>, Vec<String>) {
    // Return a Result-like structure for the snapshot
    match setup_preprocessor_test_with_diagnostics(src) {
        Ok((tokens, diags)) => {
            let debug_tokens = tokens.iter().map(DebugToken::from).collect();
            let debug_diags = diags.iter().map(|d| format!("{:?}: {}", d.level, d.message)).collect();
            (debug_tokens, debug_diags)
        }
        Err(e) => {
            (vec![], vec![format!("Fatal Error: {:?}", e)])
        }
    }
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

#[test]
fn test_simple_macro_definition_and_expansion() {
    let src = r#"
#define TEN 10
int x = TEN;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "10"
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    let src = r#"
#define ADD(a,b) ( (a) + (b) )
int x = ADD(3, 4);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "3"
    - kind: RightParen
      text: )
    - kind: Plus
      text: +
    - kind: LeftParen
      text: (
    - kind: Number
      text: "4"
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_variadic_macro_and_stringification() {
    let src = r#"
#define LOG(fmt, ...) printf(fmt, __VA_ARGS__)
#define STR(x) #x
const char* s = STR(hello_world);
LOG("value=%d\n", 5);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"hello_world\""
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"value=%d\\n\""
    - kind: Comma
      text: ","
    - kind: Number
      text: "5"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "###);
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "8"
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_macro_redefinition_warning_or_override() {
    let src = r#"
#define X 1
#define X 2
int x = X;
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r###"
    - - kind: Identifier
        text: int
      - kind: Identifier
        text: x
      - kind: Assign
        text: "="
      - kind: Number
        text: "2"
      - kind: Semicolon
        text: ;
    - - "Warning: Redefinition of macro 'X'"
    "###);
}

#[test]
fn test_predefined_macros_present() {
    let src = r#"
const int a = __STDC__;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: int
    - kind: Identifier
      text: a
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_error_directive_produces_failure() {
    let src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r###"
    - "Fatal Error: ErrorDirective(\"\\\"this should be reported\\\"\")"
    "###);
}

#[test]
fn test_complex_macro_expansion_and_recursion_limit() {
    let src = r#"
#define ID(x) x
#define A ID(ID(ID(1)))
int x = A;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_token_pasting() {
    let src = r#"
#define PASTE(a,b) a ## b
int foobar = 1;
int x = PASTE(foo, bar);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: foobar
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Identifier
      text: foobar
    - kind: Semicolon
      text: ;
    "###);
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "0"
    - kind: Semicolon
      text: ;
    "###);
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: result
    - kind: Assign
      text: "="
    - kind: Number
      text: "42"
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_file_macro() {
    let src = r#"
const char* f = __FILE__;
"#;
    let tokens = setup_pp_snapshot(src);
    // Note: setup_preprocessor_test uses "<test>" as the filename
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: f
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"<test>\""
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_pragma_operator_removes_tokens() {
    let src = r#"
_Pragma("STDC FP_CONTRACT ON")
int x = 1;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
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

    let debug_tokens: Vec<DebugToken> = significant_tokens.iter().map(DebugToken::from).collect();

    insta::assert_yaml_snapshot!(debug_tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: a
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
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

    let debug_tokens: Vec<DebugToken> = significant_tokens.iter().map(DebugToken::from).collect();

    insta::assert_yaml_snapshot!(debug_tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: a
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: a
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "###);
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "0"
    - kind: RightParen
      text: )
    - kind: Plus
      text: +
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_object_macro_with_parentheses_in_replacement() {
    let src = r#"
#define NULL ((void*)0)
int x = NULL;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: LeftParen
      text: (
    - kind: Identifier
      text: void
    - kind: Star
      text: "*"
    - kind: RightParen
      text: )
    - kind: Number
      text: "0"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "###);
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
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r###"
    - - kind: Identifier
        text: int
      - kind: Identifier
        text: x
      - kind: Assign
        text: "="
      - kind: Number
        text: "1"
      - kind: Semicolon
        text: ;
      - kind: Identifier
        text: int
      - kind: Identifier
        text: y
      - kind: Assign
        text: "="
      - kind: Number
        text: "2"
      - kind: Semicolon
        text: ;
    - []
    "###);
}

#[test]
fn test_line_directive_with_diagnostics() {
    let src = r#"
#line 50 "test.c"
invalid syntax here
"#;
    let result = setup_preprocessor_test_with_diagnostics(src);
    assert!(result.is_ok());
}

#[test]
fn test_invalid_line_directive() {
    let src = r#"
#line invalid
int x = 1;
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r###"
    - "Fatal Error: InvalidLineDirective"
    "###);
}

#[test]
fn test_line_directive_zero_line_number() {
    let src = r#"
#line 0
int x = 1;
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r###"
    - "Fatal Error: InvalidLineDirective"
    "###);
}

#[test]
fn test_line_directive_malformed_filename() {
    let src = r#"
#line 100 invalid_filename
int x = 1;
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r###"
    - "Fatal Error: InvalidLineDirective"
    "###);
}

#[test]
fn test_multiline_macro_definition_only() {
    let src = r#"
#define EMPTY(X)  \
  X               \
  X
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"[]");
}

#[test]
fn test_token_pasting_with_empty_argument() {
    let src = r#"
#define P(A,B) A ## B
int x = P(foo,);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Identifier
      text: foo
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_macro_argument_prescan_bug() {
    let src = r#"
#define STR(x) #x
#define XSTR(x) STR(x)
#define FOO 42
const char* s = XSTR(FOO);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"42\""
    - kind: Semicolon
      text: ;
    "###);
}

// New test for __FILE__ and __LINE__ dynamic behavior
#[test]
fn test_dynamic_file_and_line_macros() {
    let src = r#"
#line 10 "foo.c"
int line = __LINE__;
char* file = __FILE__;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r###"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: line
    - kind: Assign
      text: "="
    - kind: Number
      text: "10"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: file
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"foo.c\""
    - kind: Semicolon
      text: ;
    "###);
}

#[test]
fn test_missing_include_file() {
    let src = r#"
#include "nonexistent.h"
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r###"
    - "Fatal Error: FileNotFound"
    "###);
}
