use crate::pp::PPConfig;
use crate::tests::pp_common::{
    setup_pp_snapshot, setup_pp_snapshot_with_diags, setup_pp_snapshot_with_diags_and_config,
    setup_preprocessor_test_with_diagnostics,
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
    let config = PPConfig {
        current_time: Some(Utc.with_ymd_and_hms(2026, 1, 28, 0, 0, 0).unwrap()),
        ..PPConfig::default()
    };
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

#[test]
fn test_gnu_comma_swallowing_va_args() {
    let src = r#"
#define LOG(fmt, ...) printf(fmt, ##__VA_ARGS__)
LOG("foo");
LOG("bar", 1);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"foo\""
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"bar\""
    - kind: Comma
      text: ","
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "#);
}

// Regressions
#[test]
fn test_recursive_macro_expansion_regression() {
    let src = r#"
#define CAT2(a, b) a ## b
#define CAT(a, b) CAT2(a, b)
#define AB(x) CAT(x, y)
int res = AB(x);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: res
    - kind: Assign
      text: "="
    - kind: Identifier
      text: xy
    - kind: Semicolon
      text: ;
    "#);
}

// Magic Macros
#[test]
fn test_magic_macros() {
    let src = r#"
__LINE__
__FILE__
__COUNTER__
__COUNTER__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "2"
    - kind: StringLiteral
      text: "\"<test>\""
    - kind: Number
      text: "0"
    - kind: Number
      text: "1"
    "#);
}

// Placemarkers
#[test]
fn test_placemarker_concatenation() {
    let src = r#"
#define M(a, b) a ## b
M(, 1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_placemarker_concatenation_with_prefix() {
    let src = r#"
#define M(a, b) X a ## b
M(, 1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: X
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_placemarker_concatenation_chained() {
    let src = r#"
#define M(a, b, c) a ## b ## c
M(, , C)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: C
    ");
}

// GCC Compatibility
#[test]
fn test_gcc_version_macros() {
    let src = r#"
__GNUC__
__GNUC_MINOR__
__GNUC_PATCHLEVEL__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "4"
    - kind: Number
      text: "2"
    - kind: Number
      text: "1"
    "#);
}

// Regression Tests for TinyExpr Fixes
#[test]
fn test_concat_with_empty_argument() {
    let src = r#"
#define __CONCAT(x,y) x ## y
__CONCAT(a,)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: a
    ");
}

#[test]
fn test_gcc_extension_keywords() {
    let src = r#"
__extension__
__restrict
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"[]");
}

// Macro Redefinition Tests (C11 6.10.3)
#[test]
fn test_identical_macro_redefinition_no_warning() {
    // C11 6.10.3: Identical macro redefinition is allowed without warning.
    // All whitespace separations are considered identical.
    let src = r#"
#define FOO 42
#define FOO 42
FOO
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Number
        text: "42"
    - []
    "#);
}

#[test]
fn test_different_macro_redefinition_warns() {
    // Different macro redefinition should produce a warning
    let src = r#"
#define FOO 42
#define FOO 43
FOO
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Number
        text: "43"
    - - "Warning: Redefinition of macro 'FOO'"
    "#);
}

#[test]
fn test_undef_builtin_macro_should_warn() {
    let src = r#"
#undef __DATE__
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Warning: Undefining built-in macro '__DATE__'""#);
}
