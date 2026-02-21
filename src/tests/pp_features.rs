use super::pp_common::*;
use insta::assert_yaml_snapshot;

#[test]
fn test_has_builtin() {
    let src = r#"
#if __has_builtin(__builtin_expect)
    has_expect
#else
    no_expect
#endif

#if __has_builtin(__builtin_non_existent)
    has_non_existent
#else
    no_non_existent
#endif

#define EXPECT __builtin_expect
#if __has_builtin(EXPECT)
    has_expect_macro
#endif
"#;
    assert_yaml_snapshot!(setup_pp_snapshot(src), 
    @"
    - kind: Identifier
      text: has_expect
    - kind: Identifier
      text: no_non_existent
    - kind: Identifier
      text: has_expect_macro
    ");
}

#[test]
fn test_has_feature() {
    let src = r#"
#if __has_feature(c_static_assert)
    has_static_assert
#endif

#if __has_feature(c_generic_selection)
    has_generic_selection
#endif

#if __has_feature(non_existent_feature)
    has_non_existent
#else
    no_non_existent
#endif
"#;
    assert_yaml_snapshot!(setup_pp_snapshot(src), @r"
    - kind: Identifier
      text: has_static_assert
    - kind: Identifier
      text: has_generic_selection
    - kind: Identifier
      text: no_non_existent
    ");
}

#[test]
fn test_has_attribute() {
    let src = r#"
#if __has_attribute(aligned)
    has_aligned
#else
    no_aligned
#endif
"#;
    assert_yaml_snapshot!(setup_pp_snapshot(src), @r"
    - kind: Identifier
      text: no_aligned
    ");
}

#[test]
fn test_has_include_next() {
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    let dir1 = TempDir::new().unwrap();
    let dir2 = TempDir::new().unwrap();

    let h1_path = dir1.path().join("header.h");
    {
        let mut file = File::create(&h1_path).unwrap();
        writeln!(
            file,
            r#"
#if __has_include_next("header.h")
    found_next
    #include_next "header.h"
#else
    no_next
#endif
"#
        )
        .unwrap();
    }

    let h2_path = dir2.path().join("header.h");
    {
        let mut file = File::create(&h2_path).unwrap();
        writeln!(file, "final_header").unwrap();
    }

    let main_path = dir1.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, r#"#include "header.h""#).unwrap();
    }

    let mut config = crate::pp::PPConfig::default();
    config.quoted_include_paths.push(dir1.path().to_path_buf());
    config.quoted_include_paths.push(dir2.path().to_path_buf());

    let (mut sm, mut diag) = crate::tests::test_utils::setup_sm_and_diag();
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();
    let mut pp = crate::pp::Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(source_id, &config).unwrap();

    let debug_tokens: Vec<DebugToken> = tokens
        .iter()
        .filter(|t| !matches!(t.kind, crate::pp::PPTokenKind::Eof | crate::pp::PPTokenKind::Eod))
        .map(DebugToken::from)
        .collect();

    assert_yaml_snapshot!(debug_tokens, @r"
    - kind: Identifier
      text: found_next
    - kind: Identifier
      text: final_header
    ");
}
