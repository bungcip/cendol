use super::*;
use crate::source_manager::SourceId;
use std::num::NonZeroU32;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId(NonZeroU32::new(1).unwrap());
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
/// Test comprehensive line splicing scenarios
#[test]
fn test_line_splicing_comprehensive() {
    // Basic line splicing
    let source = "hel\\
lo
hel\\
lo\\
world
123\\
456
\"hello\\
world\"
";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, 
        ("hello", PPTokenKind::Identifier(_)),
        ("helloworld", PPTokenKind::Identifier(_)),
        ("123456", PPTokenKind::Number(_)),
        ("\"helloworld\"", PPTokenKind::StringLiteral(_)),
    );


    // Line splicing with whitespace
    let source = "hel  \\
    lo";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("hel", PPTokenKind::Identifier(_)));


    // No line splicing (regular newline)
    let source = "hello\nworld";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, 
        ("hello", PPTokenKind::Identifier(_)),
        ("world", PPTokenKind::Identifier(_)),
    );

    // Line splicing at end of buffer
    let source = "test\\";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("test", PPTokenKind::Identifier(_)));


    // Line splicing with CRLF
    let source = "hel\\\r\nlo";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("hello", PPTokenKind::Identifier(_)));

    // Line splicing with CR
    let source = "hel\\\rlo";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("hello", PPTokenKind::Identifier(_)));

    // Line splicing with CR at end
    let source = "test\\\r";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("test", PPTokenKind::Identifier(_)));

    // Test next_char with line splicing
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.next_char(), Some(b'b'));
    assert_eq!(lexer.next_char(), None);

    // Test peek_char with line splicing
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);
    assert_eq!(lexer.peek_char(), Some(b'a'));
    assert_eq!(lexer.position, 0);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.position, 1);
    assert_eq!(lexer.peek_char(), Some(b'b'));
    assert_eq!(lexer.position, 1);
}


/// Test that PPLexer can produce all punctuation tokens
#[test]
fn test_all_punctuation_tokens() {
    let source = "+ - * / % & | ^ ! ~ < > <= >= == != << >> = += -= *= /= %= &= |= ^= <<= >>= ++ -- -> . ? : , ; ( ) [ ] { } ... && || # ##";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("+", PPTokenKind::Plus),
        ("-", PPTokenKind::Minus),
        ("*", PPTokenKind::Star),
        ("/", PPTokenKind::Slash),
        ("%", PPTokenKind::Percent),
        ("&", PPTokenKind::And),
        ("|", PPTokenKind::Or),
        ("^", PPTokenKind::Xor),
        ("!", PPTokenKind::Not),
        ("~", PPTokenKind::Tilde),
        ("<", PPTokenKind::Less),
        (">", PPTokenKind::Greater),
        ("<=", PPTokenKind::LessEqual),
        (">=", PPTokenKind::GreaterEqual),
        ("==", PPTokenKind::Equal),
        ("!=", PPTokenKind::NotEqual),
        ("<<", PPTokenKind::LeftShift),
        (">>", PPTokenKind::RightShift),
        ("=", PPTokenKind::Assign),
        ("+=", PPTokenKind::PlusAssign),
        ("-=", PPTokenKind::MinusAssign),
        ("*=", PPTokenKind::StarAssign),
        ("/=", PPTokenKind::DivAssign),
        ("%=", PPTokenKind::ModAssign),
        ("&=", PPTokenKind::AndAssign),
        ("|=", PPTokenKind::OrAssign),
        ("^=", PPTokenKind::XorAssign),
        ("<<=", PPTokenKind::LeftShiftAssign),
        (">>=", PPTokenKind::RightShiftAssign),
        ("++", PPTokenKind::Increment),
        ("--", PPTokenKind::Decrement),
        ("->", PPTokenKind::Arrow),
        (".", PPTokenKind::Dot),
        ("?", PPTokenKind::Question),
        (":", PPTokenKind::Colon),
        (",", PPTokenKind::Comma),
        (";", PPTokenKind::Semicolon),
        ("(", PPTokenKind::LeftParen),
        (")", PPTokenKind::RightParen),
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("{", PPTokenKind::LeftBrace),
        ("}", PPTokenKind::RightBrace),
        ("...", PPTokenKind::Ellipsis),
        ("&&", PPTokenKind::LogicAnd),
        ("||", PPTokenKind::LogicOr),
        ("#", PPTokenKind::Hash),
        ("##", PPTokenKind::HashHash),
    );
}

/// Test that PPLexer can produce all keyword tokens
#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("if", PPTokenKind::Identifier(_)),
        ("ifdef", PPTokenKind::Identifier(_)),
        ("ifndef", PPTokenKind::Identifier(_)),
        ("elif", PPTokenKind::Identifier(_)),
        ("else", PPTokenKind::Identifier(_)),
        ("endif", PPTokenKind::Identifier(_)),
        ("define", PPTokenKind::Identifier(_)),
        ("undef", PPTokenKind::Identifier(_)),
        ("include", PPTokenKind::Identifier(_)),
        ("line", PPTokenKind::Identifier(_)),
        ("pragma", PPTokenKind::Identifier(_)),
        ("error", PPTokenKind::Identifier(_)),
        ("warning", PPTokenKind::Identifier(_)),
    );
}

/// Test that PPLexer can produce all literal tokens
#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("variable", PPTokenKind::Identifier(_)),
        ("\"string\"", PPTokenKind::StringLiteral(_)),
        ("'c'", PPTokenKind::CharLiteral(_, _)),
        ("123", PPTokenKind::Number(_)),
    );
}

/// Test that adjacent string literals are not combined in preprocessor stage
#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let mut lexer = create_test_pp_lexer(source);

    // First string literal
    let token1 = lexer.next_token().unwrap();
    match token1.kind {
        PPTokenKind::StringLiteral(symbol) => {
            assert_eq!(symbol.as_str(), "\"hello\"");
        }
        _ => panic!("Expected first string literal token"),
    }

    // Second string literal (should be separate, not combined)
    let token2 = lexer.next_token().unwrap();
    match token2.kind {
        PPTokenKind::StringLiteral(symbol) => {
            assert_eq!(symbol.as_str(), "\"world\"");
        }
        _ => panic!("Expected second string literal token"),
    }

    // Should be no more tokens
    assert!(lexer.next_token().is_none());
}

/// Test that single # tokens always have STARTS_PP_LINE flag set
#[test]
fn test_hash_starts_pp_line() {
    let source = "#";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

/// Test that indented # tokens have STARTS_PP_LINE flag set
#[test]
fn test_indented_hash_starts_pp_line() {
    let source = "  #";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

/// Test that ## tokens do not have STARTS_PP_LINE flag set
#[test]
fn test_hashhash_no_starts_pp_line() {
    let source = "##";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash);
    assert!(!token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}


/// Test wide character literals with L, u, U prefixes
#[test]
fn test_wide_character_literals() {
    let source = "L'a' u'b' U'c' '\\0'";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("L'a'", PPTokenKind::CharLiteral(97, _)), // 'a'
        ("u'b'", PPTokenKind::CharLiteral(98, _)), // 'b'
        ("U'c'", PPTokenKind::CharLiteral(99, _)), // 'c'
        ("'\\0'", PPTokenKind::CharLiteral(0, _)),
    );
}

/// Test wide string literals with L, u, U prefixes
#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer,
        ("L\"hello\"", PPTokenKind::StringLiteral(_)),
        ("u\"world\"", PPTokenKind::StringLiteral(_)),
        ("U\"test\"", PPTokenKind::StringLiteral(_)),
    );

    // Should be no more tokens
    assert!(lexer.next_token().is_none());
}
