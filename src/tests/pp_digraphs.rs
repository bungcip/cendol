use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraph_basic() {
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
fn test_digraph_directive() {
    let source = "%:define FOO 1\nFOO";
    let mut lexer = create_test_pp_lexer(source);

    // Test that %: has the STARTS_PP_LINE flag.
    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert!(t1.flags.contains(PPTokenFlags::STARTS_PP_LINE));

    let t2 = lexer.next_token().unwrap();
    assert!(matches!(t2.kind, PPTokenKind::Identifier(_)));
    assert_eq!(lexer.get_token_text(&t2), "define");
}

#[test]
fn test_digraph_in_macro() {
    let source = r#"
#define GLUE(a, b) a %:%: b
GLUE(1, 2)
"#;
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "12"
    "#);
}

#[test]
fn test_digraph_with_splices() {
    // Digraphs should be recognized if they are split by a splice because splices are removed in phase 2.
    let source = "<\\\n: %\\\n>";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("[", PPTokenKind::LeftBracket), ("}", PPTokenKind::RightBrace),);
}

#[test]
fn test_percent_colon_not_hash_hash() {
    // %: followed by % should be Hash then Percent
    let source = "%:%";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("#", PPTokenKind::Hash), ("%", PPTokenKind::Percent),);
}

#[test]
fn test_complex_digraph_usage() {
    let source = r#"
%:define STR(x) %:x
STR(hello)
"#;
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"hello\""
    "#);
}

#[test]
fn test_digraph_in_expression() {
    // Test that digraphs are correctly handled in a more complex context.
    let source = r#"
int main() <%
    int arr<:5:>;
    arr<:0:> = 1;
    return arr<:0:>;
%>
"#;
    let tokens = setup_pp_snapshot(source);
    // Just verify it doesn't crash and generates expected tokens
    assert!(tokens.iter().any(|t| t.text == "{"));
    assert!(tokens.iter().any(|t| t.text == "}"));
    assert!(tokens.iter().any(|t| t.text == "["));
    assert!(tokens.iter().any(|t| t.text == "]"));
}
