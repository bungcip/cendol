use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_undef_extra_tokens() {
    let src = "#undef FOO extra";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: ExpectedEod, span: SourceSpan(2199023255563) }""#);
}

#[test]
fn test_undef_eof_no_newline() {
    // This covers the None => Ok(()) branch of expect_eod
    // where the directive is terminated by EOF without a trailing Eod token from newline
    let src = "#undef FOO";
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    // Should be no errors
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
