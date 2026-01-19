use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_pragma_operator_push_pop() {
    let src = r#"
#define M 1
int a = M;
_Pragma("push_macro(\"M\")")
#undef M
#define M 2
int b = M;
_Pragma("pop_macro(\"M\")")
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
