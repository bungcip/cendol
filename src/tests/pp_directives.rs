use crate::tests::pp_common::{assert_pp, check_diag, setup_multi_file_pp_snapshot, setup_pp_snapshot_with_diags};

#[test]
fn test_error_directive_produces_failure() {
    let src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;
    check_diag(src, "ErrorDirective");
}

#[test]
fn test_warning_directive() {
    let src = r#"
#warning "this is a warning"
OK
"#;
    assert_pp(src, "OK");
    check_diag(src, "this is a warning");
}

#[test]
fn test_line_directive_presumed_location() {
    let src = r#"
// This is line 2
#line 100 "mapped.c"
// This is now logical line 101
OK
"#;
    assert_pp(src, "OK");
}

#[test]
fn test_invalid_line_directives() {
    check_diag("#line invalid\nOK", "InvalidLineDirective");
    check_diag("#line 0\nOK", "InvalidLineDirective");
    check_diag("#line 100 invalid_filename\nOK", "InvalidLineDirective");
}

#[test]
fn test_unknown_pragma_warns() {
    let src = r#"
#pragma unknown_pragma
"#;
    check_diag(src, "Unknown pragma: unknown_pragma");
}

#[test]
fn test_null_directive() {
    let src = r#"
#
#
OK
"#;
    assert_pp(src, "OK");
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
    assert_pp(src, "OK");
}

// Pragma Tests
#[test]
fn test_pragma_message() {
    let src = r#"#pragma message("Hello World")"#;
    check_diag(src, "Hello World");
    // Should produce no tokens
    let (tokens, _) = setup_pp_snapshot_with_diags(src);
    assert!(tokens.is_empty());
}

#[test]
fn test_pragma_warning() {
    let src = r#"#pragma warning("This is a warning")"#;
    check_diag(src, "This is a warning");
}

#[test]
fn test_pragma_error() {
    let src = r#"#pragma error("This is an error")"#;
    check_diag(src, "PragmaError(\"This is an error\")");
}

// _Pragma Operator
#[test]
fn test_pragma_operator() {
    // Basic _Pragma
    let src1 = r#"_Pragma("message(\"Hello Pragma Operator\")")"#;
    check_diag(src1, "Hello Pragma Operator");
    let (tokens1, _) = setup_pp_snapshot_with_diags(src1);
    assert!(tokens1.is_empty());

    // _Pragma inside macro
    let src2 = r#"
#define M _Pragma("message(\"Inside Macro\")")
M
    "#;
    check_diag(src2, "Inside Macro");
    let (tokens2, _) = setup_pp_snapshot_with_diags(src2);
    assert!(tokens2.is_empty());

    // _Pragma inside #if
    let src3 = r#"
#if _Pragma("message(\"Inside If\")") 1
#endif
    "#;
    check_diag(src3, "Inside If");
    let (tokens3, _) = setup_pp_snapshot_with_diags(src3);
    assert!(tokens3.is_empty());
}

#[test]
fn test_pragma_once_via_pragma_operator() {
    let files = vec![
        ("header.h", "_Pragma(\"once\")\nOK"),
        ("main.c", "#include \"header.h\"\n#include \"header.h\""),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    // Should only have one OK token (pragma once prevents duplicate)
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "OK");
}

// push_macro / pop_macro
#[test]
fn test_push_pop_macro() {
    // Defined macro
    let src1 = r#"
#define M 1
#pragma push_macro("M")
#undef M
#define M 2
#pragma pop_macro("M")
M
"#;
    assert_pp(src1, "1");

    // Undefined macro
    let src2 = r#"
#pragma push_macro("M")
#define M 1
#pragma pop_macro("M")
M
"#;
    assert_pp(src2, "M");
}

// EOD (End of Directive) Tests
#[test]
fn test_eod_extra_tokens() {
    // #undef with extra tokens
    check_diag("#undef FOO extra", "ExpectedEod");

    // #else with extra tokens
    let else_src = r#"
#if 1
#else extra
#endif
"#;
    check_diag(else_src, "ExpectedEod");

    // #endif with extra tokens
    let endif_src = r#"
#if 1
#endif extra
"#;
    check_diag(endif_src, "ExpectedEod");

    // #include with extra tokens
    check_diag("#include <stddef.h> extra", "ExpectedEod");
}

#[test]
fn test_undef_eof_no_newline() {
    let src = "#undef FOO";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(diags.is_empty(), "Expected no diagnostics, got: {diags:?}");
}

#[test]
fn test_pragma_gcc_poison() {
    let src = r#"
#pragma GCC poison foo bar
int foo = 1;
int baz = 2;
int bar = 3;
"#;
    let (_tokens, diags) = setup_pp_snapshot_with_diags(src);
    assert!(!diags.is_empty(), "expected diagnostics due to poisoned identifiers");
    let diag_str = format!("{:?}", diags);
    assert!(
        diag_str.contains("attempt to use poisoned identifier 'foo'"),
        "expected poisoned identifier error for foo"
    );
    assert!(
        diag_str.contains("attempt to use poisoned identifier 'bar'"),
        "expected poisoned identifier error for bar"
    );
    assert!(!diag_str.contains("baz"), "should not have error for baz");
}
