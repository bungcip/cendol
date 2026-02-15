use crate::tests::pp_common::{setup_pp_snapshot, setup_pp_snapshot_with_diags};

#[test]
fn test_elif_basic_true() {
    let src = r#"
#if 0
FAIL
#elif 1
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK
    "#);
}

#[test]
fn test_elif_basic_false() {
    let src = r#"
#if 0
FAIL
#elif 0
FAIL
#else
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK
    "#);
}

#[test]
fn test_elif_skipped() {
    let src = r#"
#if 1
OK
#elif 1
FAIL
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK
    "#);
}

#[test]
fn test_multiple_elifs() {
    let src = r#"
#if 0
FAIL_1
#elif 0
FAIL_2
#elif 1
OK
#elif 1
FAIL_3
#else
FAIL_4
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK
    "#);
}

#[test]
fn test_elif_after_else() {
    let src = r#"
#if 0
#else
#elif 1
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"
    - "Fatal Error: PPError { kind: ElifAfterElse, span: SourceSpan(2199023255566) }"
    "#);
}

#[test]
fn test_elif_without_if() {
    let src = r#"
#elif 1
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"
    - "Fatal Error: PPError { kind: ElifWithoutIf, span: SourceSpan(2199023255554) }"
    "#);
}
