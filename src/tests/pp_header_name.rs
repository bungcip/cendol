use crate::tests::pp_common::*;
use insta::assert_yaml_snapshot;
use crate::pp::PPConfig;

#[test]
fn test_header_name_with_quote() {
    let temp = tempfile::tempdir().unwrap();
    let header_path = temp.path().join("foo'bar.h");
    std::fs::write(&header_path, "int ok;").unwrap();

    let mut config = PPConfig::default();
    config.angled_include_paths.push(temp.path().to_path_buf());

    let files = vec![
        ("main.c", "#include <foo'bar.h>"),
    ];

    // I need to use the config, but setup_multi_file_pp_snapshot takes config.
    // However, I need to clone the config because I can't move it if I reuse it (though here I use it once per test).

    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", Some(config));

    assert_yaml_snapshot!("quote_tokens", tokens);
    assert_yaml_snapshot!("quote_diags", diags);
}

#[test]
fn test_header_name_with_block_comment_start() {
    let temp = tempfile::tempdir().unwrap();

    // On Linux / is separator.
    let foo_dir = temp.path().join("foo");
    std::fs::create_dir(&foo_dir).unwrap();
    std::fs::write(foo_dir.join("*bar.h"), "int ok;").unwrap();

    let mut config = PPConfig::default();
    config.angled_include_paths.push(temp.path().to_path_buf());

    let files = vec![
        ("main.c", "#include <foo/*bar.h>"),
    ];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", Some(config));

    assert_yaml_snapshot!("comment_tokens", tokens);
    assert_yaml_snapshot!("comment_diags", diags);
}
