use crate::tests::pp_common::{setup_multi_file_pp_snapshot, setup_pp_snapshot, setup_pp_snapshot_with_diags};

// Pragmas: message, warning, error
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
    // The pragma error causes a fatal error in the preprocessor, so we expect
    // the diagnostic to reflect that.
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
