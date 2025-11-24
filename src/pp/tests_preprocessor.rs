use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::source_manager::SourceManager;
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple;

/// Helper function to set up preprocessor testing
fn setup_preprocessor_test(src: &str) -> Vec<PPToken> {
    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let lang_options = LangOptions {
        c11: true,
        gnu_mode: false,
        ms_extensions: false,
    };
    let target_info = Triple::host();
    let config = PreprocessorConfig {
        max_include_depth: 100,
        system_include_paths: Vec::new(),
    };

    let source_id = source_manager.add_file_bytes("<test>", src.as_bytes().to_vec());

    let mut preprocessor = Preprocessor::new(
        &mut source_manager,
        &mut diagnostics,
        lang_options,
        target_info,
        &config,
    );

    let tokens = preprocessor.process(source_id, &config).unwrap();

    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof))
        .collect();

    significant_tokens
}

/// Helper macro to assert token sequence kinds
macro_rules! assert_token_kinds {
    ($tokens:expr, $( $expected:expr ),* $(,)?) => {{
        let expected_kinds = vec![$($expected),*];
        assert_eq!($tokens.len(), expected_kinds.len(), "Token count mismatch");
        for (i, (token, expected)) in $tokens.iter().zip(expected_kinds.iter()).enumerate() {
            assert_eq!(token.kind, *expected, "Token {} kind mismatch: expected {:?}, got {:?}", i, expected, token.kind);
        }
    }};
}

#[test]
fn test_simple_macro_definition_and_expansion() {
    let src = r#"
#define TEN 10
int x = TEN;
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected kinds: Identifier("int"), Identifier("x"), Assign, Number("10"), Semicolon
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(Symbol::new("int")),
        PPTokenKind::Identifier(Symbol::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(Symbol::new("10")),
        PPTokenKind::Semicolon
    );

    // Ensure TEN was not present (it should have been expanded)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "TEN", "TEN should have been expanded");
        }
    }
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    let src = r#"
#define ADD(a,b) ( (a) + (b) )
int x = ADD(3, 4);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, (, (, 3, ), +, (, 4, ), ), ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(Symbol::new("int")),
        PPTokenKind::Identifier(Symbol::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::LeftParen,
        PPTokenKind::LeftParen,
        PPTokenKind::Number(Symbol::new("3")),
        PPTokenKind::RightParen,
        PPTokenKind::Plus,
        PPTokenKind::LeftParen,
        PPTokenKind::Number(Symbol::new("4")),
        PPTokenKind::RightParen,
        PPTokenKind::RightParen,
        PPTokenKind::Semicolon
    );

    // Ensure ADD was not present (it should have been expanded)
    for token in &significant_tokens {
        if let PPTokenKind::Identifier(sym) = &token.kind {
            assert_ne!(sym.as_str(), "ADD", "ADD should have been expanded");
        }
    }
}
