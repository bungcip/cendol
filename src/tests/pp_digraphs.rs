use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraphs_lexing() {
    // <: -> [
    // :> -> ]
    // <% -> {
    // %> -> }
    // %: -> #
    // %:%: -> ##
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
fn test_digraph_starts_pp_line() {
    let source = "%:define FOO 1";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
    assert_eq!(token.length, 2);

    test_tokens!(
        lexer,
        ("define", PPTokenKind::Identifier(_)),
        ("FOO", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
        ("", PPTokenKind::Eod),
    );
}

#[test]
fn test_digraph_not_starts_pp_line() {
    let source = "int x; %:define FOO 1";
    let mut lexer = create_test_pp_lexer(source);

    let _ = lexer.next_token(); // int
    let _ = lexer.next_token(); // x
    let _ = lexer.next_token(); // ;

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(!token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
    assert_eq!(token.length, 2);
}

#[test]
fn test_digraph_hashhash_length() {
    let source = "%:%:";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash);
    assert_eq!(token.length, 4);
}

#[test]
fn test_digraphs_in_macros() {
    let src = r#"
#define STR(x) %:x
#define JOIN(x, y) x %:%: y

STR(abc)
JOIN(a, b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_as_directive_start() {
    let src = r#"
%:ifdef UNDEFINED
FAIL
%:else
OK
%:endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}
