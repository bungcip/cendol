use crate::tests::pp_common::{setup_multi_file_pp_snapshot, setup_pp_snapshot, setup_pp_snapshot_with_diags};

#[test]
fn test_error_directive_produces_failure() {
    let src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ErrorDirective(\"\\\"this should be reported\\\"\"), span: SourceSpan(2199023255571) }""#);
}

#[test]
fn test_warning_directive() {
    let src = r#"
#warning "this is a warning"
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Identifier
        text: OK
    - - "Warning: \"this is a warning\""
    "#);
}

#[test]
fn test_line_directive_presumed_location() {
    let src = r#"
// This is line 2
#line 100 "mapped.c"
// This is now logical line 101
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r"
    - - kind: Identifier
        text: OK
    - []
    ");
}

#[test]
fn test_invalid_line_directive() {
    let src = r#"
#line invalid
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: InvalidLineDirective, span: SourceSpan(2199023255559) }""#);
}

#[test]
fn test_line_directive_zero_line_number() {
    let src = r#"
#line 0
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: InvalidLineDirective, span: SourceSpan(2199023255559) }""#);
}

#[test]
fn test_line_directive_malformed_filename() {
    let src = r#"
#line 100 invalid_filename
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: InvalidLineDirective, span: SourceSpan(2199023255563) }""#);
}

#[test]
fn test_unknown_pragma_throws_error() {
    let src = r#"
#pragma unknown_pragma
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: UnknownPragma(\"unknown_pragma\"), span: SourceSpan(2199023255561) }""#);
}

#[test]
fn test_null_directive() {
    let src = r#"
#
#
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r"
    - - kind: Identifier
        text: OK
    - []
    ");
}

#[test]
fn test_skipped_directives_coverage() {
    let src = r#"
#if 0
#define FOO 1
#undef FOO
#include "non_existent.h"
#line 100 "bad_file.c"
#pragma unknown
#error "should not error"
#warning "should not warn"
#if 1
  #error "should not error nested"
#endif
#endif
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r"
    - - kind: Identifier
        text: OK
    - []
    ");
}

// Pragma Tests
#[test]
fn test_pragma_message() {
    let src = r#"#pragma message("Hello World")"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello World"
    "#);
}

#[test]
fn test_pragma_warning() {
    let src = r#"#pragma warning("This is a warning")"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Warning: This is a warning""#);
}

#[test]
fn test_pragma_error() {
    let src = r#"#pragma error("This is an error")"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(!diags.is_empty());
    assert!(diags[0].contains("PragmaError(\"This is an error\")"));
}

// _Pragma Operator
#[test]
fn test_pragma_operator_message() {
    let src = r#"_Pragma("message(\"Hello Pragma Operator\")")"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello Pragma Operator"
    "#);
}

#[test]
fn test_pragma_once_via_pragma_operator() {
    let files = vec![
        ("header.h", "_Pragma(\"once\")\nOK"),
        ("main.c", "#include \"header.h\"\n#include \"header.h\""),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

// push_macro / pop_macro
#[test]
fn test_push_pop_macro() {
    let src = r#"
#define M 1
#pragma push_macro("M")
#undef M
#define M 2
#pragma pop_macro("M")
OK
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_pragma_operator_inside_macro() {
    let src = r#"
#define M _Pragma("message(\"Inside Macro\")")
M
    "#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Inside Macro"
    "#);
}

#[test]
fn test_pragma_operator_in_if() {
    let src = r#"
#if _Pragma("message(\"Inside If\")") 1
#endif
    "#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Inside If"
    "#);
}

#[test]
fn test_push_pop_undefined_macro() {
    let src = r#"
#pragma push_macro("M")
#define M 1
#pragma pop_macro("M")
M
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: M
    ");
}

// EOD (End of Directive) Tests
#[test]
fn test_undef_extra_tokens() {
    let src = "#undef FOO extra";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ExpectedEod, span: SourceSpan(2199023255563) }""#);
}

#[test]
fn test_undef_eof_no_newline() {
    let src = "#undef FOO";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @"[]");
}

#[test]
fn test_else_extra_tokens() {
    let src = r#"
#if 1
#else extra
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ExpectedEod, span: SourceSpan(2199023255565) }""#);
}

#[test]
fn test_endif_extra_tokens() {
    let src = r#"
#if 1
#endif extra
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ExpectedEod, span: SourceSpan(2199023255566) }""#);
}

#[test]
fn test_include_extra_tokens_quoted() {
    let src = r#"#include <stddef.h> extra"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ExpectedEod, span: SourceSpan(2199023255572) }""#);
}
