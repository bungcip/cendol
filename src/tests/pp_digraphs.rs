use crate::pp::pp_lexer::PPTokenKind;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_with_sm};

#[test]
fn test_digraphs_lexical() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::LeftBracket);
    assert_eq!(t1.length, 2);

    let t2 = lexer.next_token().unwrap();
    assert_eq!(t2.kind, PPTokenKind::RightBracket);
    assert_eq!(t2.length, 2);

    let t3 = lexer.next_token().unwrap();
    assert_eq!(t3.kind, PPTokenKind::LeftBrace);
    assert_eq!(t3.length, 2);

    let t4 = lexer.next_token().unwrap();
    assert_eq!(t4.kind, PPTokenKind::RightBrace);
    assert_eq!(t4.length, 2);

    let t5 = lexer.next_token().unwrap();
    assert_eq!(t5.kind, PPTokenKind::Hash);
    assert_eq!(t5.length, 2);

    let t6 = lexer.next_token().unwrap();
    assert_eq!(t6.kind, PPTokenKind::HashHash);
    assert_eq!(t6.length, 4);
}

#[test]
fn test_digraph_directive() {
    let source = "%:define FOO 1\nFOO";
    let (tokens, _) = setup_pp_with_sm(source, None).unwrap();

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "1");
}

#[test]
fn test_digraph_pasting() {
    let source = "#define GLUE(a, b) a %:%: b\nGLUE(1, 2)";
    let (tokens, _) = setup_pp_with_sm(source, None).unwrap();

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "12");
}

#[test]
fn test_digraph_in_stringizing() {
    let source = "#define STR(x) %:x\nSTR(test)";
    let (tokens, _) = setup_pp_with_sm(source, None).unwrap();

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind, "StringLiteral");
}

#[test]
fn test_digraph_combinations() {
    // Array access and block
    let source = "int main() <% int a<:10:>; a<:0:> = 1; return 0; %>";
    let (tokens, _) = setup_pp_with_sm(source, None).unwrap();

    let kinds: Vec<_> = tokens.iter().map(|t| t.kind.as_str()).collect();

    assert!(kinds.contains(&"LeftBrace"));
    assert!(kinds.contains(&"RightBrace"));
    assert!(kinds.contains(&"LeftBracket"));
    assert!(kinds.contains(&"RightBracket"));
}
