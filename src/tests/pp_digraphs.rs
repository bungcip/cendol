use crate::pp::pp_lexer::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::*;

#[test]
fn test_digraphs_basic() {
    let mut lexer = create_test_pp_lexer("<: :> <% %> %: %:%:");

    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("<%", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("%:", PPTokenKind::Hash),
        ("%:%:", PPTokenKind::HashHash)
    );
}

#[test]
fn test_digraph_directive() {
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    // After expansion, it should just be "1"
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "1");
}

#[test]
fn test_digraph_stringification() {
    let source = "#define STR(x) #x\nSTR(<: :>)";
    let tokens = setup_pp_snapshot(source);

    assert_eq!(tokens.len(), 1);
    // The stringified version should contain the original spelling
    assert_eq!(tokens[0].text, "\"<: :>\"");
}

#[test]
fn test_digraph_edge_cases() {
    let mut lexer = create_test_pp_lexer("%:% :");

    test_tokens!(
        lexer,
        ("%:", PPTokenKind::Hash),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon)
    );
}

#[test]
fn test_digraph_not_pasting() {
    let mut lexer = create_test_pp_lexer("%: %:");

    test_tokens!(lexer, ("%:", PPTokenKind::Hash), ("%:", PPTokenKind::Hash));
}

#[test]
fn test_digraph_in_macro() {
    let source = "#define LBRACK <: \n LBRACK";
    let tokens = setup_pp_snapshot(source);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "<:");
}
