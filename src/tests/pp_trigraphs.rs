use crate::pp::PPTokenKind;
use crate::pp::pp_lexer::PPLexer;
use crate::source_manager::SourceId;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

/// Macro to test multiple token productions in sequence
macro_rules! test_tokens {
    ($lexer:expr, $( ($input:expr, $expected:pat) ),* $(,)?) => {
        $(
            let token = $lexer.next_token().unwrap();
            match token.kind {
                $expected => {
                    assert_eq!(token.get_text(), $input, "Token text mismatch for {}", stringify!($expected));
                },
                _ => panic!("Expected {:?}, got {:?}", stringify!($expected), token.kind),
            }
        )*
    };
}

#[test]
fn test_trigraphs_basic() {
    // Test all standard trigraphs
    // ??= -> #
    // ??/ -> \
    // ??' -> ^
    // ??( -> [
    // ??) -> ]
    // ??! -> |
    // ??< -> {
    // ??> -> }
    // ??- -> ~
    let source = "??= ??/ ??' ??( ??) ??! ??< ??> ??-";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        // For Unknown token, get_text() returns "?" currently.
        ("?", PPTokenKind::Unknown),
        ("^", PPTokenKind::Xor),
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("|", PPTokenKind::Or),
        ("{", PPTokenKind::LeftBrace),
        ("}", PPTokenKind::RightBrace),
        ("~", PPTokenKind::Tilde),
    );
}

#[test]
fn test_trigraph_splice() {
    // ??/ followed by newline is \ followed by newline, which is a splice.
    let source = "def??/\nine";
    let mut lexer = create_test_pp_lexer(source);

    // Should be lexed as "define"
    let token = lexer.next_token().unwrap();
    assert_eq!(
        token.kind,
        PPTokenKind::Identifier(crate::intern::StringId::new("define"))
    );
    assert_eq!(token.get_text(), "define");
}

#[test]
fn test_trigraph_in_string() {
    // Trigraphs are replaced everywhere, including inside strings.
    let source = "\"??(\"";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(
        token.kind,
        PPTokenKind::StringLiteral(crate::intern::StringId::new("\"[\""))
    );
    assert_eq!(token.get_text(), "\"[\"");
}

#[test]
fn test_no_trigraph() {
    // ?? followed by other char is not a trigraph
    let source = "??x";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Question);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Question);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Identifier(crate::intern::StringId::new("x")));
}

#[test]
fn test_escaped_question_marks() {
    // \? is not a trigraph escape (C doesn't escape ? outside strings usually, but in string it's valid escape)
    // But trigraph replacement happens in phase 1, so even if we have \??= it is \#
    let source = "\\??=";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Unknown); // Backslash
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash); // #
}
