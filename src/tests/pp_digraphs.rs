use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::*;

#[test]
fn test_digraph_punctuators() {
    let mut lexer = create_test_pp_lexer("<: :> <% %> %: %:%:");

    // Digraphs should be tokenized as their standard equivalents.
    // Note: token.get_text() for digraphs returns the standard punctuator string.
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
    let src = r#"
%:define FOO 1
int x = FOO;
"#;
    let tokens = setup_pp_snapshot(src);

    // Should be expanded correctly if %: is recognized as #
    assert_eq!(tokens.len(), 5); // int, x, =, 1, ;
    assert_eq!(tokens[0].text, "int");
    assert_eq!(tokens[3].text, "1");
}

#[test]
fn test_digraph_pasting() {
    let src = r#"
#define PASTE(a, b) a %:%: b
int xy = PASTE(x, y);
"#;
    let tokens = setup_pp_snapshot(src);

    // Should be expanded correctly if %:%: is recognized as ##
    assert_eq!(tokens.len(), 5); // int, xy, =, xy, ;
    assert_eq!(tokens[0].text, "int");
    assert_eq!(tokens[3].text, "xy");
}

#[test]
fn test_digraph_stringification() {
    let src = r#"
#define STR(x) #x
char* s = STR(<: :>);
"#;
    let tokens = setup_pp_snapshot(src);

    // Stringification of digraphs.
    // In C11 6.4.6p3: "the spelling of the preprocessing tokens [digraphs] is retained"
    // during stringification.
    assert_eq!(tokens.len(), 6); // char, *, s, =, "<: :>", ;
    assert_eq!(tokens[4].text, "\"<: :>\"");
}
