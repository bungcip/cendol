use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraph_lexing() {
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
fn test_digraph_at_start_of_line() {
    let source = "%:define X 1";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));

    test_tokens!(
        lexer,
        ("define", PPTokenKind::Identifier(_)),
        ("X", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
    );
}

#[test]
fn test_digraph_hash_hash_concatenation() {
    let src = r#"
#define CONCAT(a, b) a %:%: b
CONCAT(foo, bar)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: foobar
    ");
}

#[test]
fn test_digraph_hash_stringification() {
    let src = r#"
#define STR(x) %:x
STR(hello)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"hello\""
    "#);
}

#[test]
fn test_mixed_digraphs_and_standard() {
    let source = "<% [ ] %>";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("{", PPTokenKind::LeftBrace),
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("}", PPTokenKind::RightBrace),
    );
}

#[test]
fn test_digraph_regression_percent_colon_not_hash() {
    let source = "% :"; // with space
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("%", PPTokenKind::Percent), (":", PPTokenKind::Colon),);
}
