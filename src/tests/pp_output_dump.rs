use crate::diagnostic::DiagnosticEngine;
use crate::pp::{PPConfig, Preprocessor, dumper::PPDumper};
use crate::source_manager::SourceManager;

#[test]
fn test_dump_preprocessed_output_simple() {
    let src = r#"
int main() {
    return 0;
}
"#;
    // Set up preprocessor and source manager in the same context
    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig::default();

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None);

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);
    let tokens = preprocessor.process(source_id, &config).unwrap();

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, crate::pp::PPTokenKind::Eof | crate::pp::PPTokenKind::Eod))
        .collect();

    // Capture output into a buffer
    let mut buffer = Vec::new();

    PPDumper::new(&significant_tokens, &source_manager, false)
        .dump(&mut buffer)
        .unwrap();

    let content = String::from_utf8(buffer).unwrap();

    insta::assert_snapshot!(content, @r###"

int main() {
    return 0;
}
"###);
}

#[test]
fn test_dump_preprocessed_output_with_macros() {
    let src = r#"
#define TEN 10
int x = TEN;
"#;
    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig::default();

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None);

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);
    let tokens = preprocessor.process(source_id, &config).unwrap();

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, crate::pp::PPTokenKind::Eof | crate::pp::PPTokenKind::Eod))
        .collect();

    let mut buffer = Vec::new();

    PPDumper::new(&significant_tokens, &source_manager, false)
        .dump(&mut buffer)
        .unwrap();

    let content = String::from_utf8(buffer).unwrap();

    insta::assert_snapshot!(content, @"int x = 10;");
}

#[test]
fn test_dump_preprocessed_output_suppress_line_markers() {
    let src = r#"
#define TEN 10
int x = TEN;
"#;
    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig::default();

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None);

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);
    let tokens = preprocessor.process(source_id, &config).unwrap();

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, crate::pp::PPTokenKind::Eof | crate::pp::PPTokenKind::Eod))
        .collect();

    let mut buffer = Vec::new();

    PPDumper::new(&significant_tokens, &source_manager, true)
        .dump(&mut buffer)
        .unwrap();

    let content = String::from_utf8(buffer).unwrap();

    insta::assert_snapshot!(content, @"int x = 10;");
}
