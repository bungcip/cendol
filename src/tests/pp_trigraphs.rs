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
fn test_trigraph_replacement() {
    // ??= -> #
    // ??/ -> \
    // ??' -> ^
    // ??( -> [
    // ??) -> ]
    // ??! -> |
    // ??< -> {
    // ??> -> }
    // ??- -> ~

    let source = "??= define X ??/
1
??<
    int a ??( 5 ??) = ??' 5;
    int b = 1 ??! 2;
    int c = ??- 0;
??>
";
    let mut lexer = create_test_pp_lexer(source);

    // ??= define -> #define
    // ??/ \n -> \ \n -> (line splice)
    // 1 -> 1
    // So #define X 1
    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("define", PPTokenKind::Identifier(_)),
        ("X", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number(_)),
        ("", PPTokenKind::Eod), // End of #define line
    );

    // ??< -> {
    test_tokens!(lexer, ("{", PPTokenKind::LeftBrace));

    // int a ??( 5 ??) = ??' 5; -> int a [ 5 ] = ^ 5;
    test_tokens!(
        lexer,
        ("int", PPTokenKind::Identifier(_)),
        ("a", PPTokenKind::Identifier(_)),
        ("[", PPTokenKind::LeftBracket),
        ("5", PPTokenKind::Number(_)),
        ("]", PPTokenKind::RightBracket),
        ("=", PPTokenKind::Assign),
        ("^", PPTokenKind::Xor),
        ("5", PPTokenKind::Number(_)),
        (";", PPTokenKind::Semicolon),
    );

    // int b = 1 ??! 2; -> int b = 1 | 2;
    test_tokens!(
        lexer,
        ("int", PPTokenKind::Identifier(_)),
        ("b", PPTokenKind::Identifier(_)),
        ("=", PPTokenKind::Assign),
        ("1", PPTokenKind::Number(_)),
        ("|", PPTokenKind::Or),
        ("2", PPTokenKind::Number(_)),
        (";", PPTokenKind::Semicolon),
    );

    // int c = ??- 0; -> int c = ~ 0;
    test_tokens!(
        lexer,
        ("int", PPTokenKind::Identifier(_)),
        ("c", PPTokenKind::Identifier(_)),
        ("=", PPTokenKind::Assign),
        ("~", PPTokenKind::Tilde),
        ("0", PPTokenKind::Number(_)),
        (";", PPTokenKind::Semicolon),
    );

    // ??> -> }
    test_tokens!(lexer, ("}", PPTokenKind::RightBrace));
}

#[test]
fn test_trigraph_peek() {
    let source = "??=";
    let mut lexer = create_test_pp_lexer(source);

    // Peek should see '#'
    assert_eq!(lexer.peek_char(), Some(b'#'));

    // Next char should be '#'
    assert_eq!(lexer.next_char(), Some(b'#'));

    // Position should have advanced past '??=' (3 bytes)
    // Note: PPLexer implementation details (position) are internal,
    // but we can check next token is EOD or similar if we were tokenizing.
    // For next_char, we just check subsequent chars.
    assert_eq!(lexer.next_char(), None);
}

#[test]
fn test_trigraph_escaped_question() {
    // ?\? should not be a trigraph
    let source = "?\\?=";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        ("?", PPTokenKind::Question),
        ("?", PPTokenKind::Unknown), // Unknown token text is "?"
        ("?", PPTokenKind::Question),
        ("=", PPTokenKind::Assign),
    );
}

#[test]
fn test_trigraph_line_splicing() {
    // ??/ followed by newline should splicing
    let source = "def??/
ine";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("define", PPTokenKind::Identifier(_)));
}
