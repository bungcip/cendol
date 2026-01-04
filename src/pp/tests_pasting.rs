use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::intern::StringId;
use crate::source_manager::SourceManager;

/// Helper function to set up preprocessor testing
fn setup_preprocessor_test(src: &str) -> Vec<PPToken> {
    setup_preprocessor_test_with_diagnostics(src).unwrap().0
}

/// Helper function to set up preprocessor testing and return diagnostics
fn setup_preprocessor_test_with_diagnostics(
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
fn test_paste_numbers() {
    let src = r#"
#define PASTE(a, b) a ## b
int x = PASTE(1, 2);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 12, ;
    // 12 should be a Number token, NOT an Identifier token
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("12")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_paste_operators() {
    let src = r#"
#define PASTE(a, b) a ## b
int x = 1;
int y = x PASTE(+, +);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, x, =, 1, ;, int, y, =, x, ++, ;
    // ++ should be PPTokenKind::Increment
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("y")),
        PPTokenKind::Assign,
        PPTokenKind::Identifier(StringId::new("x")),
        PPTokenKind::Increment,
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_paste_identifiers() {
    let src = r#"
#define PASTE(a, b) a ## b
int xy = 100;
int z = PASTE(x, y);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: int, xy, =, 100, ;, int, z, =, xy, ;
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("xy")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("100")),
        PPTokenKind::Semicolon,
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("z")),
        PPTokenKind::Assign,
        PPTokenKind::Identifier(StringId::new("xy")),
        PPTokenKind::Semicolon
    );
}

#[test]
fn test_paste_number_and_identifier() {
    let src = r#"
#define PASTE(a, b) a ## b
// 1 and E1 form 1E1 which is a valid pp-number
double d = PASTE(1, E1);
"#;

    let significant_tokens = setup_preprocessor_test(src);

    // Expected: double, d, =, 1E1, ;
    // 1E1 is a Number token (float literal)
    assert_token_kinds!(
        significant_tokens,
        PPTokenKind::Identifier(StringId::new("double")),
        PPTokenKind::Identifier(StringId::new("d")),
        PPTokenKind::Assign,
        PPTokenKind::Number(StringId::new("1E1")),
        PPTokenKind::Semicolon
    );
}
