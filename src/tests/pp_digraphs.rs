use crate::pp::pp_lexer::PPTokenKind;
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
fn test_digraph_directive_starter() {
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    // Should be expanded to 1
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Number
      text: \"1\"
    ");
}

#[test]
fn test_digraph_fast_skip() {
    let source = "
%:if 0
  this is skipped;
%:else
  this is not skipped
%:endif
";
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: this
    - kind: Identifier
      text: is
    - kind: Identifier
      text: not
    - kind: Identifier
      text: skipped
    ");
}

#[test]
fn test_digraph_token_pasting() {
    let source = "#define PASTE(a, b) a %:%: b\nPASTE(x, y)";
    let tokens = setup_pp_snapshot(source);

    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: xy
    ");
}

#[test]
fn test_mixed_digraphs_and_punctuators() {
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
