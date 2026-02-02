use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_null_directive() {
    let src = r#"
#
#
OK
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags));
}
