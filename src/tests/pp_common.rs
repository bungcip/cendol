use crate::diagnostic::DiagnosticEngine;
use crate::pp::*;
use crate::source_manager::SourceManager;
use serde::Serialize;

#[derive(Serialize)]
pub struct DebugToken {
    pub kind: String,
    pub text: String,
}

impl From<&PPToken> for DebugToken {
    fn from(token: &PPToken) -> Self {
        let kind_str = match &token.kind {
            PPTokenKind::Identifier(_) => "Identifier".to_string(),
            PPTokenKind::StringLiteral(_) => "StringLiteral".to_string(),
            PPTokenKind::Number(_) => "Number".to_string(),
            PPTokenKind::CharLiteral(_, _) => "CharLiteral".to_string(),
            k => format!("{:?}", k),
        };

        DebugToken {
            kind: kind_str,
            text: token.get_text().to_string(),
        }
    }
}

pub fn setup_pp_snapshot(src: &str) -> Vec<DebugToken> {
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    tokens.iter().map(DebugToken::from).collect()
}

pub fn setup_pp_snapshot_with_diags(src: &str) -> (Vec<DebugToken>, Vec<String>) {
    setup_pp_snapshot_with_diags_and_config(src, None)
}

pub fn setup_pp_snapshot_with_diags_and_config(src: &str, config: Option<PPConfig>) -> (Vec<DebugToken>, Vec<String>) {
    // Return a Result-like structure for the snapshot
    match setup_preprocessor_test_with_diagnostics(src, config) {
        Ok((tokens, diags)) => {
            let debug_tokens = tokens.iter().map(DebugToken::from).collect();
            let debug_diags = diags.iter().map(|d| format!("{:?}: {}", d.level, d.message)).collect();
            (debug_tokens, debug_diags)
        }
        Err(e) => (vec![], vec![format!("Fatal Error: {:?}", e)]),
    }
}

pub fn setup_multi_file_pp_snapshot(
    files: Vec<(&str, &str)>,
    main_file: &str,
    config: Option<PPConfig>,
) -> (Vec<DebugToken>, Vec<String>) {
    match setup_multi_file_pp_with_diagnostics(files, main_file, config) {
        Ok((tokens, diags)) => {
            let debug_tokens = tokens.iter().map(DebugToken::from).collect();
            let debug_diags = diags.iter().map(|d| format!("{:?}: {}", d.level, d.message)).collect();
            (debug_tokens, debug_diags)
        }
        Err(e) => (vec![], vec![format!("Fatal Error: {:?}", e)]),
    }
}

/// Helper function to set up preprocessor testing and return diagnostics
pub fn setup_preprocessor_test_with_diagnostics(
    src: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    setup_multi_file_pp_with_diagnostics(vec![("<test>", src)], "<test>", config)
}

pub fn setup_multi_file_pp_with_diagnostics(
    files: Vec<(&str, &str)>,
    main_file_name: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    let (tokens, diagnostics) = setup_multi_file_pp_with_diagnostics_raw(files, main_file_name, config)?;

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    Ok((significant_tokens, diagnostics))
}

pub fn setup_multi_file_pp_with_diagnostics_raw(
    files: Vec<(&str, &str)>,
    main_file_name: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    // Initialize logging for tests
    let _ = env_logger::try_init();

    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = config.unwrap_or_else(|| PPConfig {
        max_include_depth: 100,
        ..Default::default()
    });

    let mut main_id = None;
    for (name, content) in files {
        let id = source_manager.add_buffer(content.as_bytes().to_vec(), name, None);
        if name == main_file_name {
            main_id = Some(id);
        }
    }

    let main_id = main_id.expect("Main file not found in provided files");

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);

    let result = preprocessor.process(main_id, &config);
    let diags = diagnostics.diagnostics().to_vec();
    match result {
        Ok(tokens) => Ok((tokens, diags)),
        Err(e) => {
            // Return collected diagnostics even on error
            if !diags.is_empty() {
                Ok((Vec::new(), diags))
            } else {
                Err(e)
            }
        }
    }
}

pub struct TestLexer {
    lexer: crate::pp::pp_lexer::PPLexer,
}

impl TestLexer {
    pub fn next_token(&mut self) -> Option<PPToken> {
        self.lexer.next_token()
    }
}

pub fn create_test_pp_lexer(src: &str) -> TestLexer {
    let mut source_manager = SourceManager::new();
    let id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None);
    let lexer = crate::pp::pp_lexer::PPLexer::new(id, src.as_bytes().to_vec());
    TestLexer { lexer }
}

#[macro_export]
macro_rules! test_tokens {
    ($lexer:expr, $( ($input:expr, $expected:pat) ),* $(,)?) => {
        $(
            let token = $lexer.next_token().unwrap();
            match token.kind {
                $expected => {
                    assert_eq!(token.get_text(), $input, "Token text mismatch for {}", stringify!($expected));
                },
                _ => panic!("Expected {:?}, got {:?}", stringify!($expected), token.kind),
            }
        )*
    };
}
