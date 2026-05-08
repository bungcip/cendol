use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::create_test_pp_lexer;

#[test]
fn test_digraph_lexing() {
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
fn test_digraph_stringification() {
    use crate::tests::pp_common::setup_pp_snapshot;
    let src = r#"
#define STR(x) #x
STR(<:)
STR(:>)
STR(<%)
STR(%>)
STR(%:)
STR(%:%:)
"#;
    let tokens = setup_pp_snapshot(src);

    // Each stringification should preserve the original digraph spelling
    assert_eq!(tokens[0].text, "\"<:\"");
    assert_eq!(tokens[1].text, "\":>\"");
    assert_eq!(tokens[2].text, "\"<%\"");
    assert_eq!(tokens[3].text, "\"%>\"");
    assert_eq!(tokens[4].text, "\"%:\"");
    assert_eq!(tokens[5].text, "\"%:%:\"");
}

#[test]
fn test_digraph_preprocessor_directive() {
    use crate::tests::pp_common::setup_pp_snapshot;
    let src = r#"
%:define FOO 1
#if FOO
int x;
%:endif
"#;
    let tokens = setup_pp_snapshot(src);
    assert_eq!(tokens.len(), 3); // int, x, ;
    assert_eq!(tokens[0].text, "int");
    assert_eq!(tokens[1].text, "x");
}

#[test]
fn test_digraph_token_pasting() {
    use crate::tests::pp_common::setup_pp_snapshot;
    let src = r#"
#define PASTE(a, b) a %:%: b
PASTE(foo, bar)
"#;
    let tokens = setup_pp_snapshot(src);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "foobar");
}

#[test]
fn test_digraph_mixed_with_standard() {
    let mut lexer = create_test_pp_lexer("<: [ :> ] <% { %> } %: #");
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
        ("%:", PPTokenKind::Hash),
        ("#", PPTokenKind::Hash),
    );
}
