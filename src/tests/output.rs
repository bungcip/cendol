use crate::diagnostic::DiagnosticEngine;
use crate::driver::output::OutputHandler;
use crate::pp::{PPConfig, Preprocessor};
use crate::source_manager::SourceManager;
use libc;
use std::io::{Read, Seek};
use std::os::fd::AsRawFd;
use tempfile::tempfile;

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

    let output_handler = OutputHandler::new();

    // Redirect stdout to a temp file
    let mut temp_file = tempfile().unwrap();
    let old_stdout = unsafe { libc::dup(libc::STDOUT_FILENO) };
    unsafe {
        libc::dup2(temp_file.as_raw_fd(), libc::STDOUT_FILENO);
    }

    output_handler
        .dump_preprocessed_output(&significant_tokens, false, &source_manager)
        .unwrap();

    // Restore stdout
    unsafe {
        libc::dup2(old_stdout, libc::STDOUT_FILENO);
        libc::close(old_stdout);
    }

    // Read from temp file
    temp_file.rewind().unwrap();
    let mut content = String::new();
    temp_file.read_to_string(&mut content).unwrap();

    insta::assert_snapshot!(content, @"");
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

    let output_handler = OutputHandler::new();

    let mut temp_file = tempfile().unwrap();
    let old_stdout = unsafe { libc::dup(libc::STDOUT_FILENO) };
    unsafe {
        libc::dup2(temp_file.as_raw_fd(), libc::STDOUT_FILENO);
    }

    output_handler
        .dump_preprocessed_output(&significant_tokens, false, &source_manager)
        .unwrap();

    unsafe {
        libc::dup2(old_stdout, libc::STDOUT_FILENO);
        libc::close(old_stdout);
    }

    temp_file.rewind().unwrap();
    let mut content = String::new();
    temp_file.read_to_string(&mut content).unwrap();

    insta::assert_snapshot!(content, @"");
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

    let output_handler = OutputHandler::new();

    let mut temp_file = tempfile().unwrap();
    let old_stdout = unsafe { libc::dup(libc::STDOUT_FILENO) };
    unsafe {
        libc::dup2(temp_file.as_raw_fd(), libc::STDOUT_FILENO);
    }

    output_handler
        .dump_preprocessed_output(&significant_tokens, true, &source_manager)
        .unwrap();

    unsafe {
        libc::dup2(old_stdout, libc::STDOUT_FILENO);
        libc::close(old_stdout);
    }

    temp_file.rewind().unwrap();
    let mut content = String::new();
    temp_file.read_to_string(&mut content).unwrap();

    insta::assert_snapshot!(content, @"");
}
