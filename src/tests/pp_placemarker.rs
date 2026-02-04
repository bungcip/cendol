use crate::tests::pp_common::setup_pp_snapshot;

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
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: C
    "#);
}
