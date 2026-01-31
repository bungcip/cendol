use crate::tests::pp_common::{setup_pp_snapshot, setup_pp_snapshot_with_diags};

#[test]
fn test_error_directive_produces_failure() {
    let src = r#"
#if 0
#else
#error "this should be reported"
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: ErrorDirective(\"\\\"this should be reported\\\"\")""#);
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
fn test_line_directive_with_diagnostics() {
    let src = r#"
#line 50 "test.c"
invalid syntax here
"#;
    setup_pp_snapshot(src);
}

#[test]
fn test_invalid_line_directive() {
    let src = r#"
#line invalid
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: InvalidLineDirective""#);
}

#[test]
fn test_line_directive_zero_line_number() {
    let src = r#"
#line 0
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: InvalidLineDirective""#);
}

#[test]
fn test_line_directive_malformed_filename() {
    let src = r#"
#line 100 invalid_filename
OK
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: InvalidLineDirective""#);
}

#[test]
fn test_unknown_pragma_throws_error() {
    let src = r#"
#pragma unknown_pragma
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(
        diags
            .iter()
            .any(|d| d.contains("Fatal Error: UnknownPragma") && d.contains("unknown_pragma")),
        "Expected error 'Fatal Error: UnknownPragma' containing 'unknown_pragma', got: {:?}",
        diags
    );
}
