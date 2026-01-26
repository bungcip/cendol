use crate::tests::pp_common::setup_multi_file_pp_snapshot;

#[test]
fn test_computed_include_quoted() {
    let files = vec![
        ("header.h", "int quoted = 1;"),
        (
            "main.c",
            r#"#define HEADER "header.h"
#include HEADER
"#,
        ),
    ];

    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_computed_include_angled_builtin() {
    // stdint.h is a built-in header
    let files = vec![(
        "main.c",
        r#"#define STDINT <stdint.h>
#include STDINT
"#,
    )];

    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    // We expect successful inclusion, which yields many tokens.
    // To keep snapshot small, we can check that we got tokens and no error.
    let has_tokens = !tokens.is_empty();
    let has_errors = diags.iter().any(|d| d.contains("Error"));

    assert!(has_tokens, "Should have tokens from stdint.h");
    assert!(!has_errors, "Should not have errors: {:?}", diags);
}

#[test]
fn test_computed_include_nested_macros() {
    let files = vec![
        ("nested.h", "int nested = 1;"),
        (
            "main.c",
            r#"#define BASE "nested.h"
#define MID BASE
#define TOP MID
#include TOP
"#,
        ),
    ];

    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_computed_include_invalid_expansion() {
    let files = vec![(
        "main.c",
        r#"#define BAD 123
#include BAD
"#,
    )];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_computed_include_empty() {
    let files = vec![(
        "main.c",
        r#"#define EMPTY
#include EMPTY
"#,
    )];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_computed_include_extra_tokens_quoted() {
    let files = vec![
        ("header.h", "int quoted = 1;"),
        (
            "main.c",
            r#"#define H "header.h"
#include H extra
"#,
        ),
    ];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_computed_include_extra_tokens_angled() {
    let files = vec![
        (
            "main.c",
            r#"#define STDINT <stdint.h>
#include STDINT extra
"#,
        ),
    ];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!((tokens, diags));
}
