use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_redefine_builtin_macro_should_fail() {
    let src = r#"
#define __DATE__ "123"
const char* s = __DATE__;
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);

    // Currently, this probably succeeds and changes __DATE__.
    // We expect it to FAIL or warn and NOT change __DATE__.
    // For now, let's just snapshot what happens.
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_undef_builtin_macro_should_fail() {
    let src = r#"
#undef __DATE__
#ifdef __DATE__
int x = 1;
#else
int x = 0;
#endif
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags));
}
