use crate::pp::pp_lexer::PPTokenKind;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraphs_basic() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token() {
        tokens.push(token);
    }

    assert_eq!(tokens[0].kind, PPTokenKind::LeftBracket);
    assert_eq!(tokens[1].kind, PPTokenKind::RightBracket);
    assert_eq!(tokens[2].kind, PPTokenKind::LeftBrace);
    assert_eq!(tokens[3].kind, PPTokenKind::RightBrace);
    assert_eq!(tokens[4].kind, PPTokenKind::Hash);
    assert_eq!(tokens[5].kind, PPTokenKind::HashHash);
}

#[test]
fn test_digraph_directive() {
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "1");
}

#[test]
fn test_digraph_macro_concatenation() {
    let source = "#define CAT(a, b) a %:%: b\nCAT(1, 2)";
    let tokens = setup_pp_snapshot(source);

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "12");
}

#[test]
fn test_digraph_macro_stringize() {
    let source = "#define STR(a) %:a\nSTR(hello)";
    let tokens = setup_pp_snapshot(source);

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "\"hello\"");
}

#[test]
fn test_digraph_edge_case_hashhash() {
    // %:% should be %: (Hash) and % (Percent)
    let source = "%:%";
    let mut lexer = create_test_pp_lexer(source);

    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);

    let t2 = lexer.next_token().unwrap();
    assert_eq!(t2.kind, PPTokenKind::Percent);
}

#[test]
fn test_digraph_nested() {
    let source = "<% <: :> %>";
    let mut lexer = create_test_pp_lexer(source);

    assert_eq!(lexer.next_token().unwrap().kind, PPTokenKind::LeftBrace);
    assert_eq!(lexer.next_token().unwrap().kind, PPTokenKind::LeftBracket);
    assert_eq!(lexer.next_token().unwrap().kind, PPTokenKind::RightBracket);
    assert_eq!(lexer.next_token().unwrap().kind, PPTokenKind::RightBrace);
}
