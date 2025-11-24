use super::*;
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
                $expected => {},
                _ => panic!("Expected {:?}, got {:?}", stringify!($expected), token.kind),
            }
        )*
    };
}

/// Test line splicing: backslash followed by newline removes both characters
#[test]
fn test_line_splicing_basic() {
    let source = "hel\\
lo";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "hello"); // Should be spliced into single identifier
        }
        _ => panic!("Expected identifier token"),
    }
}

/// Test line splicing with multiple splices
#[test]
fn test_line_splicing_multiple() {
    let source = "hel\\
lo\\
world";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "helloworld"); // Should be spliced into single identifier
        }
        _ => panic!("Expected identifier token"),
    }
}

/// Test line splicing with whitespace
#[test]
fn test_line_splicing_with_whitespace() {
    let source = "hel  \\
   lo";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "hel"); // Line splicing happens, but spaces stop the identifier
        }
        _ => panic!("Expected identifier token"),
    }
}

/// Test line splicing in numbers
#[test]
fn test_line_splicing_numbers() {
    let source = "123\\
456";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::Number(symbol) => {
            assert_eq!(symbol.as_str(), "123456"); // Should be spliced into single number
        }
        _ => panic!("Expected number token"),
    }
}

/// Test that line splicing doesn't occur without backslash-newline
#[test]
fn test_no_line_splicing() {
    let source = "hello\nworld";
    let mut lexer = create_test_pp_lexer(source);

    let first_token = lexer.next_token().unwrap();
    match first_token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "hello");
        }
        _ => panic!("Expected first identifier token"),
    }

    let second_token = lexer.next_token().unwrap();
    match second_token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "world");
        }
        _ => panic!("Expected second identifier token"),
    }
}

/// Test line splicing at end of buffer
#[test]
fn test_line_splicing_end_of_buffer() {
    let source = "test\\";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::Identifier(symbol) => {
            assert_eq!(symbol.as_str(), "test");
        }
        _ => panic!("Expected identifier token"),
    }
}

/// Test that line splicing works with peek_char and next_char
#[test]
fn test_next_char_line_splicing() {
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);

    // Test that next_char properly handles line splicing
    let ch1 = lexer.next_char();
    assert_eq!(ch1, Some(b'a'));

    // After consuming 'a', we should encounter backslash-newline
    // which should be spliced, so next_char should return 'b'
    let ch2 = lexer.next_char();
    assert_eq!(ch2, Some(b'b'));

    // Should be at end now
    let ch3 = lexer.next_char();
    assert_eq!(ch3, None);
}

/// Test peek_char doesn't consume characters including line splicing
#[test]
fn test_peek_char_line_splicing() {
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);

    // Peek should return the first character without consuming
    let peeked = lexer.peek_char();
    assert_eq!(peeked, Some(b'a'));

    // Position should still be at start
    let current_pos = lexer.position;
    assert_eq!(current_pos, 0);

    // Now consume the first character
    let consumed = lexer.next_char();
    assert_eq!(consumed, Some(b'a'));
    assert_eq!(lexer.position, 1);

    // Peek again should show that line splicing will give us 'b'
    let peeked_after_splice = lexer.peek_char();
    assert_eq!(peeked_after_splice, Some(b'b'));

    // Position should still be after 'a'
    assert_eq!(lexer.position, 1);
}

/// Test line splicing in string literals
#[test]
fn test_line_splicing_in_strings() {
    let source = "\"hello\\
world\"";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    match token.kind {
        PPTokenKind::StringLiteral(symbol) => {
            assert_eq!(symbol.as_str(), "\"helloworld\""); // Line splicing in strings
        }
        _ => panic!("Expected string literal token"),
    }
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
        ("if", PPTokenKind::If),
        ("ifdef", PPTokenKind::Ifdef),
        ("ifndef", PPTokenKind::Ifndef),
        ("elif", PPTokenKind::Elif),
        ("else", PPTokenKind::Else),
        ("endif", PPTokenKind::Endif),
        ("define", PPTokenKind::Define),
        ("undef", PPTokenKind::Undef),
        ("include", PPTokenKind::Include),
        ("line", PPTokenKind::Line),
        ("pragma", PPTokenKind::Pragma),
        ("error", PPTokenKind::Error),
        ("warning", PPTokenKind::Warning),
    );
}

/// Test that PPLexer can produce all literal tokens
#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let mut lexer = create_test_pp_lexer(source);

    let token1 = lexer.next_token().unwrap();
    match token1.kind {
        PPTokenKind::Identifier(_) => {}
        _ => panic!("Expected identifier token"),
    }

    let token2 = lexer.next_token().unwrap();
    match token2.kind {
        PPTokenKind::StringLiteral(_) => {}
        _ => panic!("Expected string literal token"),
    }

    let token3 = lexer.next_token().unwrap();
    match token3.kind {
        PPTokenKind::CharLiteral(_) => {}
        _ => panic!("Expected char literal token"),
    }

    let token4 = lexer.next_token().unwrap();
    match token4.kind {
        PPTokenKind::Number(_) => {}
        _ => panic!("Expected number token"),
    }
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
