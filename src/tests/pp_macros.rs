use crate::pp::PPConfig;
use crate::tests::pp_common::{
    setup_pp_snapshot, setup_pp_snapshot_with_diags_and_config, setup_preprocessor_test_with_diagnostics,
};
use chrono::{TimeZone, Utc};

// Basic macro tests
#[test]
fn test_simple_macro_definition_and_expansion() {
    let src = r#"
#define TEN OK
TEN
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    let src = r#"
#define ADD(a,b) ( (a) + (b) )
ADD(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Plus
      text: +
    - kind: LeftParen
      text: (
    - kind: Number
      text: "2"
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    "#);
}

#[test]
fn test_complex_macro_expansion_and_recursion_limit() {
    let src = r#"
#define ID(x) x
#define A ID(ID(ID(1)))
A
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_function_like_macro_not_expanded_when_not_followed_by_paren() {
    let src = r#"
#define x(y) ((y) + 1)
int x = x(0);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
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
    "#);
}

// Stringification (#)
#[test]
fn test_stringification_whitespace_handling() {
    let src = r#"
#define STR(x) #x
STR(a + b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"a + b\""
    "#);
}

#[test]
fn test_va_args_stringification() {
    let src = r#"
#define STR(...) #__VA_ARGS__
STR(a, b, c)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"a, b, c\""
    "#);
}

// Token Pasting (##)
#[test]
fn test_paste_numbers() {
    let src = r#"
#define PASTE(a,b) a ## b
PASTE(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "12"
    "#);
}

#[test]
fn test_paste_va_args() {
    let src = r#"
#define PASTE(...) prefix ## __VA_ARGS__
PASTE(a, b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: prefixa
    - kind: Comma
      text: ","
    - kind: Identifier
      text: b
    "#);
}

// Built-in Macros
#[test]
fn test_redefine_builtin_macro_should_fail() {
    let src = r#"
#define __DATE__ "123"
__DATE__
"#;
    let mut config = PPConfig::default();
    config.current_time = Some(Utc.with_ymd_and_hms(2026, 1, 28, 0, 0, 0).unwrap());
    let (tokens, diags) = setup_pp_snapshot_with_diags_and_config(src, Some(config));
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: StringLiteral
        text: "\"Jan 28 2026\""
    - - "Warning: Redefinition of built-in macro '__DATE__'"
    "#);
}

#[test]
fn test_file_macro() {
    let src = r#"
__FILE__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"<test>\""
    "#);
}

#[test]
fn test_counter_macro() {
    let src = r#"
__COUNTER__
__COUNTER__
__COUNTER__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "0"
    - kind: Number
      text: "1"
    - kind: Number
      text: "2"
    "#);
}

// Macro Argument Parsing
#[test]
fn test_brace_comma_separation() {
    let src = r#"
#define CNT(x, y) 2
CNT({1, 2})
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "2"));
}

#[test]
fn test_paren_comma_protection() {
    let src = r#"
#define ID(x) x
#if 1
(ID((1, 2)))
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "1"
    - kind: Comma
      text: ","
    - kind: Number
      text: "2"
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    - kind: Identifier
      text: OK
    "#);
}

// GNU Extensions
#[test]
fn test_gnu_named_variadic_macros() {
    let src = r#"
#define M(a, args...) args
M(1, 2, 3, 4)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "2"
    - kind: Comma
      text: ","
    - kind: Number
      text: "3"
    - kind: Comma
      text: ","
    - kind: Number
      text: "4"
    "#);
}

#[test]
fn test_gnu_comma_swallowing() {
    let src = r#"
#define M(a, args...) a, ## args
M(1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}
