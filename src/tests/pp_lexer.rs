use crate::pp::*;
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
    test_tokens!(
        lexer,
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
    test_tokens!(
        lexer,
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

    test_tokens!(
        lexer,
        ("\"hello\"", PPTokenKind::StringLiteral(_)),
        ("\"world\"", PPTokenKind::StringLiteral(_)),
    );
}

/// Test that line splicing is handled correctly in skip_whitespace_and_comments
/// This prevents regression of the bug where backslash-newline in macro definitions
/// caused Unknown tokens due to improper splicing in whitespace skipping.
#[test]
fn test_line_splicing_in_skip_whitespace() {
    // This simulates the scenario in macro definitions where backslash-newline
    // appears after skipping initial whitespace, and ensures no Unknown tokens
    let source = "   \\\n   identifier";
    let mut lexer = create_test_pp_lexer(source);

    // The lexer should skip the whitespace and handle the splicing,
    // then lex "identifier" without producing Unknown for the space after splicing
    test_tokens!(lexer, ("identifier", PPTokenKind::Identifier(_)));

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

    test_tokens!(
        lexer,
        ("L\"hello\"", PPTokenKind::StringLiteral(_)),
        ("u\"world\"", PPTokenKind::StringLiteral(_)),
        ("U\"test\"", PPTokenKind::StringLiteral(_)),
    );

    // Should be no more tokens
    assert!(lexer.next_token().is_none());
}

/// Test that Eod (End of Directive) tokens are produced at the end of directive lines
#[test]
fn test_eod_token_production() {
    // Test simple directive
    let source = "#define x 1\n";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("define", PPTokenKind::Identifier(_)),
        ("x", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number(_)),
        ("", PPTokenKind::Eod),
    );
}

/// Test that Eod tokens are produced for various directive types
#[test]
fn test_eod_for_various_directives() {
    // Test various directive types that should all end with Eod
    let test_cases = vec![
        "#ifdef TEST\n",
        "#ifndef TEST\n",
        "#elif 1\n",
        "#else\n",
        "#endif\n",
        "#include \"test.h\"\n",
        "#undef TEST\n",
        "#line 100\n",
        "#pragma once\n",
        "#error message\n",
        "#warning message\n",
    ];

    for directive in test_cases {
        let mut lexer = create_test_pp_lexer(directive);
        let tokens: Vec<_> = std::iter::from_fn(|| lexer.next_token()).collect();

        // Should have at least Hash token and Eod token
        assert!(tokens.len() >= 2, "Should have tokens for directive: {}", directive);
        assert_eq!(
            tokens[0].kind,
            PPTokenKind::Hash,
            "First token should be Hash for: {}",
            directive
        );
        assert_eq!(
            tokens.last().unwrap().kind,
            PPTokenKind::Eod,
            "Should end with Eod for directive: {}",
            directive
        );
    }
}

/// Test that Eod is produced at EOF when in directive line (clang compatibility)
#[test]
fn test_eod_at_eof_in_directive() {
    // Directive at end of file without newline
    let source = "#define x 1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("define", PPTokenKind::Identifier(_)),
        ("x", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number(_)),
        ("", PPTokenKind::Eod),
    );

    // Should be no more tokens
    assert!(lexer.next_token().is_none());
}

/// Test string literals with BMP (Basic Multilingual Plane) Unicode characters
#[test]
fn test_bmp_unicode_string_literals() {
    // Test the specific target string with mixed ASCII and BMP characters
    let source = r#"L"hello$$你好¢¢世界€€world""#;
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, (source, PPTokenKind::StringLiteral(_)));
}

/// Test various BMP character types in string literals
#[test]
fn test_various_bmp_characters() {
    let test_cases = vec![
        // Chinese characters (3-byte UTF-8 sequences)
        (r#"L"你好世界""#, "L\"你好世界\""),
        // Currency symbols (2-byte and 3-byte UTF-8 sequences)
        (r#"L"€$¢£¥""#, "L\"€$¢£¥\""),
        // Mixed ASCII and BMP
        (r#"L"hello¢world€test""#, "L\"hello¢world€test\""),
        // Extended Latin characters (2-byte UTF-8 sequences)
        (r#"L"café naïve résumé""#, "L\"café naïve résumé\""),
        // Greek characters (2-byte UTF-8 sequences)
        (r#"L"αβγδε""#, "L\"αβγδε\""),
        // Cyrillic characters (2-byte UTF-8 sequences)
        (r#"L"привет мир""#, "L\"привет мир\""),
    ];

    for (source, expected) in test_cases {
        let mut lexer = create_test_pp_lexer(source);
        test_tokens!(lexer, (expected, PPTokenKind::StringLiteral(_)));
    }
}

/// Test edge cases and special characters in string literals
#[test]
fn test_special_characters_in_strings() {
    // Test with various special characters that might cause issues
    let test_cases = vec![
        // Regular ASCII with quotes and backslashes
        (r#"L"hello \"world\" \\test""#, r#"L"hello \"world\" \\test""#),
        // Mixed quotes and special chars
        (r#"L"café's \"test\" \\value""#, r#"L"café's \"test\" \\value""#),
        // String with newlines (line splicing) - should splice the newline
        (
            r#"L"hello\
world""#,
            r#"L"helloworld""#,
        ),
        // String with all types of quotes
        (r#"""#, r#"""#),
        (r#"L"""#, r#"L"""#),
        (r#"u"""#, r#"u"""#),
        (r#"U"""#, r#"U"""#),
    ];

    for (source, expected) in test_cases {
        let mut lexer = create_test_pp_lexer(source);
        test_tokens!(lexer, (expected, PPTokenKind::StringLiteral(_)));
    }
}

/// Test UTF-8 sequences of different lengths
#[test]
fn test_utf8_sequence_lengths() {
    // 1-byte sequence (ASCII)
    let source1 = r#"L"abc""#;
    let mut lexer1 = create_test_pp_lexer(source1);
    test_tokens!(lexer1, (source1, PPTokenKind::StringLiteral(_)));

    // 2-byte sequence (extended ASCII)
    let source2 = r#"L"café""#;
    let mut lexer2 = create_test_pp_lexer(source2);
    test_tokens!(lexer2, (source2, PPTokenKind::StringLiteral(_)));

    // 3-byte sequence (BMP Chinese)
    let source3 = r#"L"你好""#;
    let mut lexer3 = create_test_pp_lexer(source3);
    test_tokens!(lexer3, (source3, PPTokenKind::StringLiteral(_)));

    // Mixed sequences
    let source4 = r#"L"café你好""#;
    let mut lexer4 = create_test_pp_lexer(source4);
    test_tokens!(lexer4, (source4, PPTokenKind::StringLiteral(_)));
}
