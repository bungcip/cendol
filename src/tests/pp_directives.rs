use crate::tests::pp_common::{assert_pp, assert_pp_diag, setup_multi_file_pp_snapshot, setup_pp_snapshot_with_diags};

// A. Error & Warning Directives
#[test]
fn test_error_and_warning_directives() {
    // Error directive
    let err_src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;
    assert_pp_diag(err_src, "ErrorDirective");

    // Warning directive
    let warn_src = r#"
#warning "this is a warning"
OK
"#;
    assert_pp(warn_src, "OK");
    assert_pp_diag(warn_src, "this is a warning");
}

// B. Line Directives
#[test]
fn test_line_directives() {
    // Valid line directive
    let valid_src = r#"
// This is line 2
#line 100 "mapped.c"
// This is now logical line 101
OK
"#;
    assert_pp(valid_src, "OK");

    // Invalid line directives
    assert_pp_diag("#line invalid\nOK", "InvalidLineDirective");
    assert_pp_diag("#line 0\nOK", "InvalidLineDirective");
    assert_pp_diag("#line 100 invalid_filename\nOK", "InvalidLineDirective");
}

// C. Pragmas
#[test]
fn test_pragmas() {
    // Unknown pragma
    assert_pp_diag("#pragma unknown_pragma\n", "Unknown pragma: unknown_pragma");

    // Pragma message
    let msg_src = r#"#pragma message("Hello World")"#;
    assert_pp_diag(msg_src, "Hello World");
    let (tokens, _) = setup_pp_snapshot_with_diags(msg_src);
    assert!(tokens.is_empty());

    // Pragma warning
    assert_pp_diag(r#"#pragma warning("This is a warning")"#, "This is a warning");

    // Pragma error
    assert_pp_diag(
        r#"#pragma error("This is an error")"#,
        "PragmaError(\"This is an error\")",
    );

    // Pragma GCC poison
    let poison_src = r#"
#pragma GCC poison foo bar
int foo = 1;
int baz = 2;
int bar = 3;
"#;
    let (_tokens, diags) = setup_pp_snapshot_with_diags(poison_src);
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

// D. Misc & Skipped Directives
#[test]
fn test_misc_directives() {
    // Null directive
    assert_pp("#\n#\nOK\n", "OK");

    // Skipped directives coverage
    let skipped_src = r#"
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
    assert_pp(skipped_src, "OK");
}

// E. _Pragma Operator
#[test]
fn test_pragma_operator_and_once() {
    // Basic _Pragma
    let src1 = r#"_Pragma("message(\"Hello Pragma Operator\")")"#;
    assert_pp_diag(src1, "Hello Pragma Operator");
    let (tokens1, _) = setup_pp_snapshot_with_diags(src1);
    assert!(tokens1.is_empty());

    // _Pragma inside macro
    let src2 = r#"
#define M _Pragma("message(\"Inside Macro\")")
M
    "#;
    assert_pp_diag(src2, "Inside Macro");
    let (tokens2, _) = setup_pp_snapshot_with_diags(src2);
    assert!(tokens2.is_empty());

    // _Pragma inside #if
    let src3 = r#"
#if _Pragma("message(\"Inside If\")") 1
#endif
    "#;
    assert_pp_diag(src3, "Inside If");
    let (tokens3, _) = setup_pp_snapshot_with_diags(src3);
    assert!(tokens3.is_empty());

    // Pragma once
    let files = vec![
        ("header.h", "_Pragma(\"once\")\nOK"),
        ("main.c", "#include \"header.h\"\n#include \"header.h\""),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    // Should only have one OK token (pragma once prevents duplicate)
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "OK");
}

// F. push_macro / pop_macro
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

// G. EOD (End of Directive) & EOF Tests
#[test]
fn test_eod_and_eof() {
    // #undef with extra tokens
    assert_pp_diag("#undef FOO extra", "ExpectedEod");

    // #else with extra tokens
    let else_src = r#"
#if 1
#else extra
#endif
"#;
    assert_pp_diag(else_src, "ExpectedEod");

    // #endif with extra tokens
    let endif_src = r#"
#if 1
#endif extra
"#;
    assert_pp_diag(endif_src, "ExpectedEod");

    // #include with extra tokens
    assert_pp_diag("#include <stddef.h> extra", "ExpectedEod");

    // undef eof no newline
    let src = "#undef FOO";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(diags.is_empty(), "Expected no diagnostics, got: {diags:?}");
}
