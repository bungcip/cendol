use crate::tests::pp_common::setup_multi_file_pp_snapshot;

#[test]
fn test_computed_include_string() {
    let files = vec![("foo.h", "OK"), ("main.c", "#define H \"foo.h\"\n#include H")];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.is_empty(), "Unexpected diagnostics: {:?}", diags);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_computed_include_angled() {
    let files = vec![("foo.h", "OK"), ("main.c", "#define H <foo.h>\n#include H")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    // Expect fatal error because of virtual file system and angled include
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("FileNotFound"),
        "Expected FileNotFound, got {}",
        diags[0]
    );
    assert!(diags[0].contains("foo.h"), "Expected foo.h in error, got {}", diags[0]);
}

#[test]
fn test_computed_include_composite() {
    let files = vec![("main.c", "#define L <\n#define R >\n#include L foo.h R")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("FileNotFound"),
        "Expected FileNotFound, got {}",
        diags[0]
    );
    assert!(diags[0].contains("foo.h"), "Expected foo.h in error, got {}", diags[0]);
}

#[test]
fn test_computed_include_empty() {
    let files = vec![("main.c", "#define E\n#include E")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("InvalidIncludePath"),
        "Expected InvalidIncludePath, got {}",
        diags[0]
    );
}

#[test]
fn test_computed_include_invalid() {
    let files = vec![("main.c", "#define I 123\n#include I")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("InvalidIncludePath"),
        "Expected InvalidIncludePath, got {}",
        diags[0]
    );
}

#[test]
fn test_computed_include_extra_tokens_string() {
    let files = vec![("foo.h", ""), ("main.c", "#define H \"foo.h\"\n#include H extra")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("ExpectedEod"),
        "Expected ExpectedEod, got {}",
        diags[0]
    );
}

#[test]
fn test_computed_include_extra_tokens_angled() {
    let files = vec![("main.c", "#define H <foo.h>\n#include H extra")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("ExpectedEod"),
        "Expected ExpectedEod, got {}",
        diags[0]
    );
}

#[test]
fn test_computed_include_missing_greater() {
    let files = vec![("main.c", "#define H <foo.h\n#include H")];
    let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("InvalidIncludePath"),
        "Expected InvalidIncludePath, got {}",
        diags[0]
    );
}
