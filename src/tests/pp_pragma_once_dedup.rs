use crate::diagnostic::DiagnosticEngine;
use crate::pp::*;
use crate::source_manager::SourceManager;

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

    let mut sm = SourceManager::new();
    let main_id = sm.add_file(&main_c, None).expect("Failed to add main.c");

    let mut diag = DiagnosticEngine::default();
    let mut config = PPConfig::default();
    config.quoted_include_paths.push(base_path.to_path_buf());

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(main_id, &config).expect("Preprocessing failed");

    // Convert tokens to string for easier verification
    let mut output = String::new();
    for token in tokens {
        if !matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
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
