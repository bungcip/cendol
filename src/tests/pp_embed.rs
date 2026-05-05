use crate::diagnostic::DiagnosticEngine;
use crate::pp::PPTokenKind;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::PPConfig;
use crate::source_manager::SourceManager;

#[test]
fn test_embed_basic() {
    let source = r#"
#embed "test.bin"
"#;
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();
    let config = PPConfig::default();

    // The source itself must be added to SourceManager
    let source_id = sm.add_buffer(
        source.as_bytes().to_vec(),
        "main.c",
        None,
        crate::source_manager::FileKind::Real,
    );

    // Add the file to be embedded
    sm.add_buffer(vec![1, 2, 3], "test.bin", None, crate::source_manager::FileKind::Real);

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(source_id, &config).unwrap();

    let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
    // 1, Comma, 2, Comma, 3, Eof
    assert_eq!(kinds.len(), 6);
    assert!(matches!(kinds[0], PPTokenKind::Number));
    assert!(matches!(kinds[1], PPTokenKind::Comma));
    assert!(matches!(kinds[2], PPTokenKind::Number));
    assert!(matches!(kinds[3], PPTokenKind::Comma));
    assert!(matches!(kinds[4], PPTokenKind::Number));
    assert!(matches!(kinds[5], PPTokenKind::Eof));
}

#[test]
fn test_embed_limit() {
    let source = r#"
#embed "test.bin" limit(2)
"#;
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();
    let config = PPConfig::default();

    let source_id = sm.add_buffer(
        source.as_bytes().to_vec(),
        "main.c",
        None,
        crate::source_manager::FileKind::Real,
    );
    sm.add_buffer(
        vec![1, 2, 3, 4],
        "test.bin",
        None,
        crate::source_manager::FileKind::Real,
    );

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(source_id, &config).unwrap();

    let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
    // 1, Comma, 2, Eof
    assert_eq!(kinds.len(), 4);
    assert!(matches!(kinds[0], PPTokenKind::Number));
    assert!(matches!(kinds[1], PPTokenKind::Comma));
    assert!(matches!(kinds[2], PPTokenKind::Number));
    assert!(matches!(kinds[3], PPTokenKind::Eof));
}

#[test]
fn test_embed_not_found() {
    let source = r#"
#embed "nonexistent.bin"
"#;
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();
    let config = PPConfig::default();

    let source_id = sm.add_buffer(
        source.as_bytes().to_vec(),
        "main.c",
        None,
        crate::source_manager::FileKind::Real,
    );

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let result = pp.process(source_id, &config);
    assert!(result.is_err());
}

#[test]
fn test_embed_macro() {
    let source = r#"
#define FILE "test.bin"
#embed FILE
"#;
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();
    let config = PPConfig::default();

    let source_id = sm.add_buffer(
        source.as_bytes().to_vec(),
        "main.c",
        None,
        crate::source_manager::FileKind::Real,
    );
    sm.add_buffer(vec![42], "test.bin", None, crate::source_manager::FileKind::Real);

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);
    let tokens = pp.process(source_id, &config).unwrap();

    let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
    // 42, Eof
    assert_eq!(kinds.len(), 2);
    assert!(matches!(kinds[0], PPTokenKind::Number));
    assert!(matches!(kinds[1], PPTokenKind::Eof));
}
