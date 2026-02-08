use crate::tests::pp_common::setup_pp_snapshot_with_diags;

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
fn test_line_directive_presumed_location() {
    let src = r#"
// This is line 2
#line 100 "mapped.c"
// This is now logical line 101
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Identifier
        text: OK
    - []
    "#);
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
