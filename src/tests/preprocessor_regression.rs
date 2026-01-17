use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_recursive_macro_expansion_regression() {
    let src = r#"
#define CAT2(a, b) a ## b
#define CAT(a, b) CAT2(a, b)
#define AB(x) CAT(x, y)
int res = AB(x);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: res
    - kind: Assign
      text: "="
    - kind: Identifier
      text: xy
    - kind: Semicolon
      text: ;
    "#);
}
