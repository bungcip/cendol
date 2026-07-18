use crate::ast::StringId;
use crate::pp::{PPConfig, Preprocessor};
use crate::tests::pp_common::setup_multi_file_pp_snapshot;
use crate::tests::test_utils::setup_sm_and_de;
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
    insta::assert_yaml_snapshot!(tokens, @"
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
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: PPDiag { kind: IncludeDepthExceeded, span: SourceSpan(3298534883337) }""#);
}

// include_next Tests
#[test]
fn test_include_next_paths() {
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
        writeln!(file, "#include_next <foo.h>").unwrap();
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
    config.angled_include_paths.push(dir2.path().to_path_buf());
    config.angled_include_paths.push(dir1.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_de();
    let source_id = sm.add_file(&main_path, None).unwrap();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let _ = pp.process(source_id).unwrap();

    assert!(pp.is_macro_defined(StringId::new("FOO_1")));
    assert!(pp.is_macro_defined(StringId::new("FOO_2")));
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

    let (mut sm, mut diag) = setup_sm_and_de();
    let source_id = sm.add_file(&main_path, None).unwrap();
    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let _ = pp.process(source_id).unwrap();

    assert!(pp.is_macro_defined(StringId::new("MY_STDDEF_WRAPPER")));
    assert!(pp.is_macro_defined(StringId::new("NULL")));
}

// Computed Include Tests
#[test]
fn test_computed_include_string() {
    let files = vec![("foo.h", "OK"), ("main.c", "#define H \"foo.h\"\n#include H")];
    let (tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert!(diags.is_empty(), "Unexpected diagnostics: {:?}", diags);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_computed_includes_errors() {
    let cases = [
        ("#define H <foo.h>\n#include H", "FileNotFound"),
        ("#define L <\n#define R >\n#include L foo.h R", "FileNotFound"),
        ("#define E\n#include E", "InvalidIncludePath"),
        ("#define I 123\n#include I", "InvalidIncludePath"),
        ("#define H \"foo.h\"\n#include H extra", "ExpectedEod"),
        ("#define H <foo.h>\n#include H extra", "ExpectedEod"),
        ("#define H <foo.h\n#include H", "InvalidIncludePath"),
    ];

    for (src, expected_err) in cases {
        let files = vec![("foo.h", ""), ("main.c", src)];
        let (_tokens, diags) = setup_multi_file_pp_snapshot(files, "main.c", None);
        assert!(
            diags.len() == 1,
            "Expected 1 diagnostic for case '{}', got {:?}",
            src,
            diags
        );
        assert!(
            diags[0].contains(expected_err),
            "Expected {}, got {}",
            expected_err,
            diags[0]
        );
    }
}

#[test]
fn test_pragma_once_path_dedup() {
    // Create a temporary directory for our test files
    let temp_dir = tempfile::tempdir().expect("Failed to create temp dir");
    let base_path = temp_dir.path();

    let header_a = base_path.join("a.h");
    let header_b = base_path.join("b.h");
    let main_c = base_path.join("main.c");

    std::fs::write(&header_a, "#pragma once\nint x;").expect("Failed to write a.h");
    // b.h includes a.h using a relative path with redundant components
    std::fs::write(&header_b, "#include \"./a.h\"\nint y;").expect("Failed to write b.h");
    // main.c includes both a.h and b.h
    std::fs::write(&main_c, "#include \"a.h\"\n#include \"b.h\"").expect("Failed to write main.c");

    let (mut sm, mut diag) = crate::tests::test_utils::setup_sm_and_de();
    let main_id = sm.add_file(&main_c, None).expect("Failed to add main.c");

    let mut config = PPConfig::default();
    config.quoted_include_paths.push(base_path.to_path_buf());

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(main_id).expect("Preprocessing failed");

    // Convert tokens to string for easier verification
    let mut output = String::new();
    for token in tokens {
        if !matches!(token.kind, crate::pp::PPTokenKind::Eod | crate::pp::PPTokenKind::Eof) {
            output.push_str(&token.get_text(pp.sm));
            output.push(' ');
        }
    }

    // Verification:
    // 'int x;' should only appear ONCE because of #pragma once and path deduplication.
    // 'int y;' should appear once.
    let x_count = output.matches("int x").count();
    let y_count = output.matches("int y").count();

    assert_eq!(
        x_count, 1,
        "int x should appear exactly once, found output: \n{}",
        output
    );
    assert_eq!(y_count, 1, "int y should appear exactly once");
}
