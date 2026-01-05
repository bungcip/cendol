use super::*;
use crate::source_manager::SourceId;

fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[test]
fn test_digraphs() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    // <: -> [
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::LeftBracket, "Expected <:");

    // :> -> ]
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::RightBracket, "Expected :>");

    // <% -> {
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::LeftBrace, "Expected <%");

    // %> -> }
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::RightBrace, "Expected %>");

    // %: -> #
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash, "Expected %:");

    // %:%: -> ##
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash, "Expected %:%:");
}

#[test]
fn test_digraph_hash_at_start_of_line() {
    let source = "%:define FOO";
    let mut lexer = create_test_pp_lexer(source);

    let t1 = lexer.next_token().unwrap(); // %: -> #

    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert!(
        t1.flags.contains(PPTokenFlags::STARTS_PP_LINE),
        "Digraph %: at start of line SHOULD set STARTS_PP_LINE"
    );
    assert!(
        lexer.in_directive_line,
        "Digraph %: at start of line SHOULD start directive line"
    );
}

#[test]
fn test_digraph_hash_in_middle_of_line() {
    let source = "int %:";
    let mut lexer = create_test_pp_lexer(source);

    let _t1 = lexer.next_token().unwrap(); // int
    let t2 = lexer.next_token().unwrap(); // %: -> #

    // %: in middle of line should NOT be a directive starter
    assert_eq!(t2.kind, PPTokenKind::Hash);
    assert!(
        !t2.flags.contains(PPTokenFlags::STARTS_PP_LINE),
        "Digraph %: in middle of line should NOT set STARTS_PP_LINE"
    );
    assert!(
        !lexer.in_directive_line,
        "Digraph %: in middle of line should NOT start directive line"
    );
}

#[test]
fn test_mixed_digraphs_and_operators() {
    let source = "< % : <:";
    let mut lexer = create_test_pp_lexer(source);

    // <
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::Less);

    // %
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::Percent);

    // :
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::Colon);

    // <: -> [
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::LeftBracket);
}
