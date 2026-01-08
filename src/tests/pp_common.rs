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
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src).unwrap();
    tokens.iter().map(DebugToken::from).collect()
}

pub fn setup_pp_snapshot_with_diags(src: &str) -> (Vec<DebugToken>, Vec<String>) {
    // Return a Result-like structure for the snapshot
    match setup_preprocessor_test_with_diagnostics(src) {
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
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    // Initialize logging for tests
    let _ = env_logger::try_init();

    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig {
        max_include_depth: 100,
        ..Default::default()
    };

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>");

    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);

    let tokens = preprocessor.process(source_id, &config)?;

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    Ok((significant_tokens, diagnostics.diagnostics().to_vec()))
}
