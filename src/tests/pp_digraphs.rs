use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::create_test_pp_lexer;

#[test]
fn test_basic_digraphs() {
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
    let src = "%:define FOO 1\nBAR";
    let mut lexer = create_test_pp_lexer(src);

    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert_eq!(lexer.get_token_text(&t1), "%:");
    assert!(t1.flags.contains(crate::pp::PPTokenFlags::STARTS_PP_LINE));

    test_tokens!(
        lexer,
        ("define", PPTokenKind::Identifier(_)),
        ("FOO", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
        ("", PPTokenKind::Eod),
        ("BAR", PPTokenKind::Identifier(_)),
    );
}

#[test]
fn test_digraph_backtracking() {
    // %: followed by something else should be Hash, then that something else
    let mut lexer = create_test_pp_lexer("%: % : %:%");

    // 1. %:
    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert_eq!(lexer.get_token_text(&t1), "%:");

    // 2. %
    let t2 = lexer.next_token().unwrap();
    assert_eq!(t2.kind, PPTokenKind::Percent);
    assert_eq!(lexer.get_token_text(&t2), "%");

    // 3. :
    let t3 = lexer.next_token().unwrap();
    assert_eq!(t3.kind, PPTokenKind::Colon);
    assert_eq!(lexer.get_token_text(&t3), ":");

    // 4. %:%
    // %: followed by % but not followed by :
    // should be %: (Hash) then % (Percent)
    let t4 = lexer.next_token().unwrap();
    assert_eq!(t4.kind, PPTokenKind::Hash);
    assert_eq!(lexer.get_token_text(&t4), "%:");

    let t5 = lexer.next_token().unwrap();
    assert_eq!(t5.kind, PPTokenKind::Percent);
    assert_eq!(lexer.get_token_text(&t5), "%");
}

#[test]
fn test_digraph_in_macro() {
    use crate::tests::pp_common::setup_pp_snapshot;

    let src = r#"
#define STR(x) %:x
#define CONCAT(x, y) x %:%: y
STR(abc)
CONCAT(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);

    // STR(abc) -> #abc -> "abc"
    // Wait, #x in macro is stringification.
    // %:x should also be stringification if it maps to Hash.

    assert_eq!(tokens[0].kind, "StringLiteral");
    assert_eq!(tokens[0].text, "\"abc\"");

    // CONCAT(1, 2) -> 1 ## 2 -> 12
    assert_eq!(tokens[1].kind, "Number");
    assert_eq!(tokens[1].text, "12");
}

#[test]
fn test_mixed_digraphs_and_standard() {
    let mut lexer = create_test_pp_lexer("[ <: { <% ] :> } %> # %: ## %:%:");
    test_tokens!(
        lexer,
        ("[", PPTokenKind::LeftBracket),
        ("<:", PPTokenKind::LeftBracket),
        ("{", PPTokenKind::LeftBrace),
        ("<%", PPTokenKind::LeftBrace),
        ("]", PPTokenKind::RightBracket),
        (":>", PPTokenKind::RightBracket),
        ("}", PPTokenKind::RightBrace),
        ("%>", PPTokenKind::RightBrace),
        ("#", PPTokenKind::Hash),
        ("%:", PPTokenKind::Hash),
        ("##", PPTokenKind::HashHash),
        ("%:%:", PPTokenKind::HashHash),
    );
}
