use crate::tests::pp_common::setup_pp_snapshot_with_diags;

#[test]
fn test_include_backslash_path() {
    let src = r#"
#include <win\path.h>
"#;
    // We expect FileNotFound, but the path should be correct (win\path.h), not win?path.h
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_include_space_path() {
    let src = r#"
#include <a b.h>
"#;
    // We expect FileNotFound, but the path should be correct (a b.h), not ab.h
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags));
}
