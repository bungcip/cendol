use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::create_test_pp_lexer;

#[test]
fn test_digraph_basic() {
    let mut lexer = create_test_pp_lexer("<: :> <% %> %: %:%:");
    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("<%", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("%:", PPTokenKind::Hash),
        ("%:%:", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraph_directive() {
    let mut lexer = create_test_pp_lexer("%:define FOO 1\nFOO");

    // Check %: as #
    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert_eq!(lexer.get_token_text(&t1), "%:");

    let t2 = lexer.next_token().unwrap();
    assert_eq!(lexer.get_token_text(&t2), "define");

    let t3 = lexer.next_token().unwrap();
    assert_eq!(lexer.get_token_text(&t3), "FOO");

    let t4 = lexer.next_token().unwrap();
    assert_eq!(lexer.get_token_text(&t4), "1");
}

#[test]
fn test_digraph_mismatch() {
    // These should NOT be digraphs
    let mut lexer = create_test_pp_lexer("< : > < % : % :");
    test_tokens!(
        lexer,
        ("<", PPTokenKind::Less),
        (":", PPTokenKind::Colon),
        (">", PPTokenKind::Greater),
        ("<", PPTokenKind::Less),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
    );
}

#[test]
fn test_digraph_nested() {
    let mut lexer = create_test_pp_lexer("<% <: :> %>");
    test_tokens!(
        lexer,
        ("<%", PPTokenKind::LeftBrace),
        ("<:", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("%>", PPTokenKind::RightBrace),
    );
}
