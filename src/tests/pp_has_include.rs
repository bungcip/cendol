use crate::tests::pp_common::{setup_multi_file_pp_snapshot, setup_pp_snapshot};

#[test]
fn test_has_include_builtin() {
    let src = r#"
#if __has_include(<stddef.h>)
int x = 1;
#else
int x = 0;
#endif

#if __has_include("stddef.h")
int y = 1;
#else
int y = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: y
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_has_include_missing() {
    let src = r#"
#if __has_include(<nonexistent.h>)
int x = 1;
#else
int x = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "0"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_has_include_with_files() {
    let files = vec![
        ("header.h", "int z = 3;"),
        (
            "main.c",
            r#"
#if __has_include("header.h")
int x = 1;
#else
int x = 0;
#endif

#if __has_include(<header.h>)
int y = 1;
#else
int y = 0;
#endif
"#,
        ),
    ];
    // Note: angled search usually doesn't include current dir unless -I. is passed.
    // In our test setup, we rely on behavior of HeaderSearch in tests.
    // Usually setup_multi_file_pp_snapshot doesn't add -I., so <header.h> might fail if not in system paths.
    // However, quoted "header.h" should pass.

    // For this test we only assert on x being 1.
    // We expect y to be 0 unless we configure search paths, but let's check behavior.

    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: y
    - kind: Assign
      text: "="
    - kind: Number
      text: "0"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_has_include_macro_argument_not_expanded() {
    let src = r#"
#define HEADER <stddef.h>
#if __has_include(HEADER)
int x = 1;
#else
int x = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_has_include_complex_path() {
    let src = r#"
#if __has_include(<sys/types.h>)
// we assume sys/types.h doesn't exist in our mock environment
int x = 1;
#else
int x = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "0"
    - kind: Semicolon
      text: ;
    "#);
}
