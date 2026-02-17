use crate::pp::{PPConfig, Preprocessor};
use crate::tests::pp_common::setup_multi_file_pp_snapshot;
use crate::tests::test_utils::setup_sm_and_diag;
use std::fs::File;
use std::io::Write;
use tempfile::TempDir;

// Basic Include tests
#[test]
fn test_include_same_file_twice_without_pragma_once() {
    let files = vec![
        ("header_test_twice.h", "OK"),
        (
            "main.c",
            "#include \"header_test_twice.h\"\n#include \"header_test_twice.h\"",
        ),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_circular_include_in_memory() {
    let files = vec![
        ("mem_a.h", "#include \"mem_b.h\""),
        ("mem_b.h", "#include \"mem_a.h\""),
        ("mem_main.c", "#include \"mem_a.h\""),
    ];
    let config = PPConfig {
        max_include_depth: 10,
        ..Default::default()
    };
    let (_, diags) = setup_multi_file_pp_snapshot(files, "mem_main.c", Some(config));
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPError { kind: IncludeDepthExceeded, span: SourceSpan(3298534883337) }""#);
}

// include_next Tests
#[test]
fn test_include_next_quoted() {
    let dir1 = TempDir::new().unwrap();
    let dir2 = TempDir::new().unwrap();

    let foo1_path = dir1.path().join("foo.h");
    {
        let mut file = File::create(&foo1_path).unwrap();
        writeln!(file, "#define FOO_1 1").unwrap();
    }

    let foo2_path = dir2.path().join("foo.h");
    {
        let mut file = File::create(&foo2_path).unwrap();
        writeln!(file, "#include_next \"foo.h\"").unwrap();
        writeln!(file, "#define FOO_2 1").unwrap();
    }

    let main_path = dir2.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, "#include \"foo.h\"").unwrap();
    }

    let mut config = PPConfig::default();
    config.quoted_include_paths.push(dir2.path().to_path_buf());
    config.quoted_include_paths.push(dir1.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_diag();
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let _ = pp.process(source_id, &config).unwrap();

    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_1")));
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_2")));
}

#[test]
fn test_include_next_angled() {
    let dir1 = TempDir::new().unwrap();
    let dir2 = TempDir::new().unwrap();

    let foo1_path = dir1.path().join("foo.h");
    {
        let mut file = File::create(&foo1_path).unwrap();
        writeln!(file, "#define FOO_1 1").unwrap();
    }

    let foo2_path = dir2.path().join("foo.h");
    {
        let mut file = File::create(&foo2_path).unwrap();
        writeln!(file, "#include_next <foo.h>").unwrap();
        writeln!(file, "#define FOO_2 1").unwrap();
    }

    let main_path = dir2.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, "#include <foo.h>").unwrap();
    }

    let mut config = PPConfig::default();
    config.angled_include_paths.push(dir2.path().to_path_buf());
    config.angled_include_paths.push(dir1.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_diag();
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let _ = pp.process(source_id, &config).unwrap();

    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_1")));
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_2")));
}

#[test]
fn test_include_next_builtin() {
    let dir = TempDir::new().unwrap();

    let stddef_path = dir.path().join("stddef.h");
    {
        let mut file = File::create(&stddef_path).unwrap();
        writeln!(file, "#define MY_STDDEF_WRAPPER 1").unwrap();
        writeln!(file, "#include_next <stddef.h>").unwrap();
    }

    let main_path = dir.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, "#include <stddef.h>").unwrap();
    }

    let mut config = PPConfig::default();
    config.angled_include_paths.push(dir.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_diag();
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let _ = pp.process(source_id, &config).unwrap();

    assert!(pp.is_macro_defined(&crate::ast::StringId::new("MY_STDDEF_WRAPPER")));
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("NULL")));
}

// Computed Include Tests
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
    assert!(diags.len() == 1, "Expected 1 diagnostic, got {:?}", diags);
    assert!(
        diags[0].contains("FileNotFound"),
        "Expected FileNotFound, got {}",
        diags[0]
    );
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
