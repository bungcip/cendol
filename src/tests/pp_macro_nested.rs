use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_nested_macro_expansion_in_args() {
    let src = r#"
#define CAST(t, e) ((t)(e))
#define CAST_U(o) CAST(unsigned, o)

CAST(unsigned, CAST_U(i))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}
