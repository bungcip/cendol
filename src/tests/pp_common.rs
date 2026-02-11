use crate::pp::*;
use crate::source_manager::SourceManager;
use crate::tests::test_utils::setup_sm_and_diag;
use serde::Serialize;

#[derive(Serialize)]
pub(crate) struct DebugToken {
    pub(crate) kind: String,
    pub(crate) text: String,
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

pub(crate) fn setup_pp_snapshot(src: &str) -> Vec<DebugToken> {
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    tokens.iter().map(DebugToken::from).collect()
}

pub(crate) fn setup_pp_snapshot_with_diags(src: &str) -> (Vec<DebugToken>, Vec<String>) {
    setup_pp_snapshot_with_diags_and_config(src, None)
}

pub(crate) fn setup_pp_snapshot_with_diags_and_config(src: &str, config: Option<PPConfig>) -> (Vec<DebugToken>, Vec<String>) {
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

pub(crate) fn setup_multi_file_pp_snapshot(
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
pub(crate) fn setup_preprocessor_test_with_diagnostics(
    src: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    setup_multi_file_pp_with_diagnostics(vec![("<test>", src)], "<test>", config)
}

pub(crate) fn setup_multi_file_pp_with_diagnostics(
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

pub(crate) fn setup_multi_file_pp_with_diagnostics_raw(
    files: Vec<(&str, &str)>,
    main_file_name: &str,
    config: Option<PPConfig>,
) -> Result<(Vec<PPToken>, Vec<crate::diagnostic::Diagnostic>), PPError> {
    // Initialize logging for tests
    let _ = env_logger::try_init();

    let (mut sm, mut diag) = setup_sm_and_diag();
    let config = config.unwrap_or_else(|| PPConfig {
        max_include_depth: 100,
        ..Default::default()
    });

    let mut main_id = None;
    for (name, content) in files {
        let id = sm.add_buffer(content.as_bytes().to_vec(), name, None);
        if name == main_file_name {
            main_id = Some(id);
        }
    }

    let main_id = main_id.expect("Main file not found in provided files");

    let mut preprocessor = Preprocessor::new(&mut sm, &mut diag, &config);

    let tokens = preprocessor.process(main_id, &config)?;
    Ok((tokens, diag.diagnostics().to_vec()))
}

pub(crate) struct TestLexer {
    lexer: crate::pp::pp_lexer::PPLexer,
}

impl TestLexer {
    pub(crate) fn next_token(&mut self) -> Option<PPToken> {
        self.lexer.next_token()
    }
}

pub(crate) fn create_test_pp_lexer(src: &str) -> TestLexer {
    let mut source_manager = SourceManager::new();
    let id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>", None);
    let lexer = crate::pp::pp_lexer::PPLexer::new(id, std::sync::Arc::from(src.as_bytes().to_vec()));
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
