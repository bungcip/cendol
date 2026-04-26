use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraph_bracket() {
    let source = "<: :>";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("[", PPTokenKind::LeftBracket), ("]", PPTokenKind::RightBracket),);
}

#[test]
fn test_digraph_brace() {
    let source = "<% %>";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("{", PPTokenKind::LeftBrace), ("}", PPTokenKind::RightBrace),);
}

#[test]
fn test_digraph_hash() {
    let source = "%: %:%:";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("#", PPTokenKind::Hash), ("##", PPTokenKind::HashHash),);
}

#[test]
fn test_digraph_hash_directive() {
    let src = r#"
%:define FOO 1
#if FOO
OK
%:endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_digraph_mixture() {
    let source = "<: %> <% :>";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        ("[", PPTokenKind::LeftBracket),
        ("}", PPTokenKind::RightBrace),
        ("{", PPTokenKind::LeftBrace),
        ("]", PPTokenKind::RightBracket),
    );
}
