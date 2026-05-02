use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_basic_digraphs() {
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
fn test_digraph_hash_starts_pp_line() {
    let source = "%:";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_indented_digraph_hash_starts_pp_line() {
    let source = "  %:";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_digraph_directive() {
    let src = r#"
%:define FOO 1
#if FOO
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_digraph_hashhash_in_macro() {
    let src = r#"
#define CONCAT(a, b) a %:%: b
CONCAT(x, y)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: xy
    ");
}

#[test]
fn test_digraph_not_in_literal() {
    let source = r#""<:" '<%'"#;
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("\"<:\"", PPTokenKind::StringLiteral),
        ("'<%'", PPTokenKind::CharLiteral(_)),
    );
}

#[test]
fn test_digraph_mixed_with_normal() {
    let source = "<% int a<:1:>; %>";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("{", PPTokenKind::LeftBrace),
        ("int", PPTokenKind::Identifier(_)),
        ("a", PPTokenKind::Identifier(_)),
        ("[", PPTokenKind::LeftBracket),
        ("1", PPTokenKind::Number),
        ("]", PPTokenKind::RightBracket),
        (";", PPTokenKind::Semicolon),
        ("}", PPTokenKind::RightBrace),
    );
}
