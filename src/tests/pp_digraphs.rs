use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_all_digraph_tokens() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

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
fn test_digraph_directive_starter() {
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Number
      text: \"1\"
    ");
}

#[test]
fn test_digraph_token_pasting() {
    let source = r#"
%:define PASTE(a, b) a %:%: b
PASTE(foo, bar)
"#;
    let tokens = setup_pp_snapshot(source);

    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: foobar
    ");
}

#[test]
fn test_digraph_stringification() {
    let source = r#"
%:define STR(x) %:x
STR(foo)
"#;
    let tokens = setup_pp_snapshot(source);

    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"foo\""
    "#);
}

#[test]
fn test_digraph_mixed_with_standard() {
    let source = "<: [ :> ] <% { %> }";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        ("[", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("]", PPTokenKind::RightBracket),
        ("<%", PPTokenKind::LeftBrace),
        ("{", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("}", PPTokenKind::RightBrace),
    );
}

#[test]
fn test_percent_colon_backtracking() {
    let source = "%:%";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("%:", PPTokenKind::Hash), ("%", PPTokenKind::Percent),);
}

#[test]
fn test_digraph_in_macro_body() {
    let source = r#"
#define BRACKETS <: :>
BRACKETS
"#;
    let tokens = setup_pp_snapshot(source);

    insta::assert_yaml_snapshot!(tokens, @"
    - kind: LeftBracket
      text: \"<:\"
    - kind: RightBracket
      text: \":>\"
    ");
}
