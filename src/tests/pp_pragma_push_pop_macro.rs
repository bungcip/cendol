use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_push_pop_macro() {
    let src = r#"
#define M 1
int a = M;
#pragma push_macro("M")
#undef M
#define M 2
int b = M;
#pragma pop_macro("M")
int c = M;
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Identifier
        text: int
      - kind: Identifier
        text: a
      - kind: Assign
        text: "="
      - kind: Number
        text: "1"
      - kind: Semicolon
        text: ;
      - kind: Identifier
        text: int
      - kind: Identifier
        text: b
      - kind: Assign
        text: "="
      - kind: Number
        text: "2"
      - kind: Semicolon
        text: ;
      - kind: Identifier
        text: int
      - kind: Identifier
        text: c
      - kind: Assign
        text: "="
      - kind: Number
        text: "1"
      - kind: Semicolon
        text: ;
    - []
    "#);
}

#[test]
fn test_push_pop_macro_undefined() {
    let src = r#"
#pragma push_macro("M")
#define M 1
int a = M;
#pragma pop_macro("M")
#ifdef M
int b = 1;
#else
int b = 0;
#endif
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Identifier
        text: int
      - kind: Identifier
        text: a
      - kind: Assign
        text: "="
      - kind: Number
        text: "1"
      - kind: Semicolon
        text: ;
      - kind: Identifier
        text: int
      - kind: Identifier
        text: b
      - kind: Assign
        text: "="
      - kind: Number
        text: "0"
      - kind: Semicolon
        text: ;
    - []
    "#);
}
