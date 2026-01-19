use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_pragma_message() {
    let src = r#"
#pragma message("Hello World")
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello World"
    "#);
}

#[test]
fn test_pragma_warning() {
    let src = r#"
#pragma warning("This is a warning")
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Warning: This is a warning"
    "#);
}

#[test]
fn test_pragma_error() {
    let src = r#"
#pragma error("This is an error")
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Fatal Error: PragmaError(\"This is an error\")"
    "#);
}

#[test]
fn test_pragma_message_concat() {
    let src = r#"
#pragma message("Hello" " " "World")
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello World"
    "#);
}

#[test]
fn test_pragma_message_macro_expansion() {
    let src = r#"
#define MSG "Hello Macro"
#pragma message(MSG)
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello Macro"
    "#);
}

#[test]
fn test_pragma_message_missing_parens() {
    let src = r#"
#pragma message "Hello"
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Fatal Error: InvalidDirective"
    "#);
}

#[test]
fn test_pragma_operator_message() {
    let src = r#"
_Pragma("message(\"Hello Pragma Operator\")")
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - []
    - - "Note: Hello Pragma Operator"
    "#);
}
