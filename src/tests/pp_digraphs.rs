use crate::pp::pp_lexer::PPLexer;
use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::source_manager::SourceId;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

/// Macro to test multiple token productions in sequence
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

#[test]
fn test_digraphs_basic() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("{", PPTokenKind::LeftBrace),
        ("}", PPTokenKind::RightBrace),
        ("#", PPTokenKind::Hash),
        ("##", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraphs_mixed_with_operators() {
    // Check that < still works as Less, % as Percent, etc.
    let source = "< % : <:";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("<", PPTokenKind::Less),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
        ("[", PPTokenKind::LeftBracket),
    );
}

#[test]
fn test_digraph_hash_starts_line() {
    // %: define
    let source = "%: define";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));

    let token = lexer.next_token().unwrap();
    assert!(matches!(token.kind, PPTokenKind::Identifier(_)));
    assert_eq!(token.get_text(), "define");

    // Check that EOD is produced
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Eod);
}

#[test]
fn test_digraph_hashhash_no_starts_line() {
    // %:%:
    let source = "%:%:";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash);
    assert!(!token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_digraph_hash_indented() {
    // Indented %: should also start line
    let source = "   %: define";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}
