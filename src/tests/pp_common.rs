use std::sync::Arc;

use crate::diagnostic::Diagnostic;
use crate::pp::pp_lexer::PPLexer;
use crate::pp::*;
use crate::source_manager::{FileKind, SourceManager};
use crate::tests::test_utils::setup_sm_and_de;
use serde::Serialize;

#[derive(Serialize)]
pub struct DebugToken {
    pub kind: String,
    pub text: String,
}

impl DebugToken {
    pub(crate) fn from_token(token: &PPToken, sm: &SourceManager) -> Self {
        let name = token.kind.kind_name();
        let kind = if name.is_empty() {
            format!("{:?}", token.kind)
        } else {
            name.to_string()
        };

        let text = token.get_text_with_sm(sm).into_owned();

        DebugToken { kind, text }
    }
}

pub(crate) fn setup_pp_snapshot(src: &str) -> Vec<DebugToken> {
    let (tokens, _) = setup_pp_with_sm(src, None).unwrap();
    tokens
}

pub(crate) fn setup_pp_snapshot_with_diags(src: &str) -> (Vec<DebugToken>, Vec<String>) {
    setup_pp_snapshot_with_diags_and_config(src, None)
}

pub(crate) fn setup_pp_snapshot_with_diags_and_config(
    src: &str,
    config: Option<PPConfig>,
) -> (Vec<DebugToken>, Vec<String>) {
    // Return a Result-like structure for the snapshot
    match setup_pp_with_sm_and_diagnostics(src, config) {
        Ok((tokens, _sm, diags)) => {
            let debug_diags = diags.iter().map(|d| format!("{:?}: {}", d.level, d.message)).collect();
            (tokens, debug_diags)
        }
        Err(e) => (vec![], vec![format!("Fatal Error: {:?}", e)]),
    }
}

pub(crate) fn setup_multi_file_pp_snapshot(
    files: Vec<(&str, &str)>,
    main_file: &str,
    config: Option<PPConfig>,
) -> (Vec<DebugToken>, Vec<String>) {
    match setup_multi_file_pp_with_sm_and_diagnostics(files, main_file, config) {
        Ok((tokens, _sm, diags)) => {
            let debug_diags = diags.iter().map(|d| format!("{:?}: {}", d.level, d.message)).collect();
            (tokens, debug_diags)
        }
        Err(e) => (vec![], vec![format!("Fatal Error: {:?}", e)]),
    }
}

/// Helper function to set up preprocessor testing and return sm
fn setup_pp_with_sm(src: &str, config: Option<PPConfig>) -> Result<(Vec<DebugToken>, SourceManager), PPError> {
    let (tokens, sm, _) = setup_multi_file_pp_with_sm_and_diagnostics(vec![("<test>", src)], "<test>", config)?;
    Ok((tokens, sm))
}

pub(crate) fn setup_pp_with_sm_and_diagnostics(
    src: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<DebugToken>, SourceManager, Vec<Diagnostic>), PPError> {
    setup_multi_file_pp_with_sm_and_diagnostics(vec![("<test>", src)], "<test>", config)
}

fn setup_multi_file_pp_with_sm_and_diagnostics(
    files: Vec<(&str, &str)>,
    main_file_name: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<DebugToken>, SourceManager, Vec<Diagnostic>), PPError> {
    let (tokens, sm, diagnostics) = setup_multi_file_pp_with_diagnostics_raw(files, main_file_name, config)?;

    let debug_tokens: Vec<DebugToken> = tokens
        .iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .map(|t| DebugToken::from_token(t, &sm))
        .collect();

    Ok((debug_tokens, sm, diagnostics))
}

fn setup_multi_file_pp_with_diagnostics_raw(
    files: Vec<(&str, &str)>,
    main_file_name: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, SourceManager, Vec<Diagnostic>), PPError> {
    // Initialize logging for tests
    let _ = env_logger::try_init();

    let (mut sm, mut diag) = setup_sm_and_de();
    let config = config.unwrap_or_else(|| PPConfig {
        max_include_depth: 100,
        ..Default::default()
    });

    let mut main_id = None;
    for (name, content) in files {
        let id = sm.add_buffer(content.as_bytes().to_vec(), name, None, FileKind::Real);
        if name == main_file_name {
            main_id = Some(id);
        }
    }

    let main_id = main_id.expect("Main file not found in provided files");

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);

    let tokens = pp.process(main_id, &config)?;
    Ok((tokens, sm, diag.diagnostics.clone()))
}

pub struct TestLexer {
    lexer: PPLexer,
}

impl TestLexer {
    pub(crate) fn next_token(&mut self) -> Option<PPToken> {
        self.lexer.next_token()
    }

    pub(crate) fn get_token_text(&self, token: &PPToken) -> std::borrow::Cow<'_, str> {
        token.get_text_from_buffer(&self.lexer.buffer)
    }
}

pub(crate) fn create_test_pp_lexer(src: &str) -> TestLexer {
    let mut source_manager = SourceManager::new();
    let id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None, FileKind::Real);
    let lexer = PPLexer::new(id, Arc::from(src.as_bytes().to_vec()));
    TestLexer { lexer }
}

#[macro_export]
macro_rules! test_tokens {
    ($lexer:expr, $( ($input:expr, $expected:pat) ),* $(,)?) => {
        $(
            let token = $lexer.next_token().unwrap();
            match token.kind {
                $expected => {
                    assert_eq!($lexer.get_token_text(&token).as_ref(), $input, "Token text mismatch for {}", stringify!($expected));
                },
                _ => panic!("Expected {:?}, got {:?}", stringify!($expected), token.kind),
            }
        )*
    };
}
