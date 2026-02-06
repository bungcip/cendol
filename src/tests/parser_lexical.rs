use crate::ast::literal_parsing;
use crate::driver::artifact::CompilePhase;
use crate::parser::TokenKind;
use crate::tests::test_utils;
use std::collections::BTreeMap;

/// Helper function to test lexing from string to TokenKind
/// This tests the full pipeline: string -> PPToken -> TokenKind
fn setup_lexer(input: &str) -> Vec<TokenKind> {
    setup_lexer_with_eof(input, false)
}

/// Helper function to test lexing from string to TokenKind, optionally including EndOfFile
fn setup_lexer_with_eof(source: &str, include_eof: bool) -> Vec<TokenKind> {
    let phase = CompilePhase::Lex;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let tokens = artifact.lexed.clone().unwrap();

    if include_eof {
        tokens.into_iter().map(|t| t.kind).collect()
    } else {
        tokens
            .into_iter()
            .filter(|t| !matches!(t.kind, TokenKind::EndOfFile))
            .map(|t| t.kind)
            .collect()
    }
}

#[test]
fn test_c11_keywords() {
    // Test all C11 keywords including C11-specific ones
    #[rustfmt::skip]
    let keywords = vec![
        "auto", "break", "case", "char", "const", "continue", "default", "do",
        "double", "else", "enum", "extern", "float", "for", "goto", "if",
        "inline", "int", "long", "register", "restrict", "return", "short",
        "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
        "unsigned", "void", "volatile", "while",
        // C11 specific keywords
        "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic",
        "_Noreturn", "_Static_assert", "_Thread_local",
    ];

    let mut map = BTreeMap::new();
    for keyword in keywords {
        let tokens = setup_lexer(keyword);
        assert_eq!(tokens.len(), 1, "Expected 1 token for keyword: {}", keyword);
        map.insert(keyword, tokens[0]);
    }
    insta::assert_yaml_snapshot!(map);
}

#[test]
fn test_operators_and_punctuation() {
    let operators = vec![
        "+", "-", "*", "/", "%", "&", "|", "^", "!", "~",
        "<", ">", "<=", ">=", "==", "!=",
        "<<", ">>",
        "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
        "++", "--",
        "->", ".",
        "?", ":",
        ",", ";", "...",
        "(", ")", "[", "]", "{", "}",
        "&&", "||",
    ];

    let mut map = BTreeMap::new();
    for text in operators {
        let tokens = setup_lexer(text);
        assert_eq!(tokens.len(), 1, "Expected 1 token for operator: {}", text);
        map.insert(text, tokens[0]);
    }
    insta::assert_yaml_snapshot!(map);
}

#[test]
fn test_literals() {
    // Integer constants
    let int_literals = vec![
        "42", "0x1A", "077",
        // C11 integer suffixes - decimal
        "1ll", "42u", "123l", "456ul", "789lu", "1000ull", "2000llu",
        // C11 integer suffixes - hexadecimal
        "0x1Au", "0xFFll", "0x10UL", "0x20LU", "0x40ULL", "0x80LLU",
        // C11 integer suffixes - octal
        "077u", "0123l", "0777ul", "0123lu", "0777ull", "0123llu",
        // Case insensitive suffixes
        "1LL", "42U", "123L", "456UL", "789LU", "1000ULL", "2000LLU",
    ];

    // Float constants
    let float_literals = vec![
        "1.5", "1.23e-4", "0x1.2p3",
    ];

    // Character constants
    let char_literals = vec![
        "'a'", "'\\n'",
    ];

    // String literals
    let string_literals = vec![
        "\"hello\"", "\"world\\n\"",
    ];

    let mut map = BTreeMap::new();

    // Helper to insert with prefix
    let mut insert = |prefix: &str, items: Vec<&str>| {
        for text in items {
            let tokens = setup_lexer(text);
            assert_eq!(tokens.len(), 1, "Expected 1 token for literal: {}", text);
            map.insert(format!("{} {}", prefix, text), tokens[0]);
        }
    };

    insert("int", int_literals);
    insert("float", float_literals);
    insert("char", char_literals);
    insert("string", string_literals);

    insta::assert_yaml_snapshot!(map);
}

#[test]
fn test_identifiers() {
    let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

    let mut map = BTreeMap::new();
    for ident in identifiers {
        let tokens = setup_lexer(ident);
        assert_eq!(tokens.len(), 1, "Expected 1 token for identifier: {}", ident);
        map.insert(ident, tokens[0]);
    }
    insta::assert_yaml_snapshot!(map);
}

#[test]
fn test_string_literal_concatenation() {
    // Test adjacent string literal concatenation (C11 6.4.5)
    let test_cases = vec![
        // Basic concatenation
        ("\"hello\" \"world\"", "helloworld"),
        // With whitespace between
        ("\"hello\"   \"world\"", "helloworld"),
        // Multiple concatenations
        ("\"a\" \"b\" \"c\"", "abc"),
        // With escape sequences
        ("\"hello\\n\" \"world\"", "hello\nworld"),
        // Mixed quotes and content
        ("\"start\" \" middle \" \"end\"", "start middle end"),
    ];

    let mut map = BTreeMap::new();
    for (input, expected_content) in test_cases {
        let token_kinds = setup_lexer(input);
        assert_eq!(
            token_kinds.len(),
            1,
            "Expected 1 token for concatenated string: {}",
            input
        );

        match &token_kinds[0] {
            TokenKind::StringLiteral(symbol) => {
                let actual_content = symbol.as_str();
                assert_eq!(
                    actual_content, expected_content,
                    "String concatenation failed for input: {}",
                    input
                );
                map.insert(input, actual_content.to_string());
            }
            _ => panic!("Expected StringLiteral token for input: {}", input),
        }
    }
    insta::assert_yaml_snapshot!(map);

    // Test that non-adjacent strings are not concatenated
    let token_kinds = setup_lexer("\"hello\" ; \"world\"");
    insta::assert_yaml_snapshot!(token_kinds);
}

#[test]
fn test_special_tokens() {
    // EndOfFile - empty string should produce EndOfFile when included
    let token_kinds = setup_lexer_with_eof("", true);
    insta::assert_yaml_snapshot!(token_kinds, @r"
    - EndOfFile
    ");

    // Unknown - unrecognized character should produce Unknown
    let token_kinds = setup_lexer("@");
    insta::assert_yaml_snapshot!(token_kinds, @r"
    - Unknown
    ");
}

#[test]
fn test_string_escapes_edge_cases() {
    // Test edge cases in string literal unescaping
    let test_cases = vec![
        // \x with no digits - should keep the x
        ("\"\\xg\"", "\\xg"),
        // \x with invalid unicode value (overflow) - should use replacement character
        // \x110000 is > 0x10FFFF
        ("\"\\x110000\"", "\u{FFFD}"),
        // \? escape
        ("\"\\?\"", "?"),
        // Unknown escape sequence (e.g. \q) - should keep the character
        ("\"\\q\"", "q"),
    ];

    let mut map = BTreeMap::new();
    for (input, expected) in test_cases {
        let token_kinds = setup_lexer(input);
        assert_eq!(token_kinds.len(), 1, "Expected 1 token for input: {}", input);

        if let TokenKind::StringLiteral(sid) = token_kinds[0] {
            assert_eq!(sid.as_str(), expected, "Failed for input: {}", input);
            map.insert(input, sid.as_str().to_string());
        } else {
            panic!("Expected StringLiteral for input: {}", input);
        }
    }
    insta::assert_yaml_snapshot!(map);
}

#[test]
fn test_literal_parsing_edge_cases() {
    // Test parse_c11_integer_literal edge cases
    assert!(
        literal_parsing::parse_c11_integer_literal("0x").is_none(),
        "0x should fail"
    );
    assert!(
        literal_parsing::parse_c11_integer_literal("u").is_none(),
        "Suffix only should fail"
    );

    // Test parse_c11_float_literal edge cases
    assert!(
        literal_parsing::parse_c11_float_literal("").is_none(),
        "Empty string should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x").is_none(),
        "Hex prefix only should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x.").is_none(),
        "Hex prefix with dot should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x..p0").is_none(),
        "Hex float with double dot should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x1G").is_none(),
        "Hex float with invalid char should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x.p0").is_none(),
        "Hex float with no digits should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x1p").is_none(),
        "Hex float missing exponent digits should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x1p+").is_none(),
        "Hex float missing exponent digits after sign should fail"
    );
    assert!(
        literal_parsing::parse_c11_float_literal("0x1p+A").is_none(),
        "Hex float exponent cut by non-digit should fail"
    );

    // Test parse_char_literal edge cases
    assert!(
        literal_parsing::parse_char_literal("").is_none(),
        "Empty char literal should fail"
    );

    // Test unescape_string edge cases
    // Short octal escape
    assert_eq!(
        literal_parsing::unescape_string("\\1"),
        "\x01",
        "Short octal escape failed"
    );
    // Octal escape cut by non-octal digit
    assert_eq!(
        literal_parsing::unescape_string("\\19"),
        "\x019",
        "Octal escape cut by non-octal failed"
    );
    // Hex escape cut by non-hex digit
    assert_eq!(
        literal_parsing::unescape_string("\\x1G"),
        "\x01G",
        "Hex escape cut by non-hex failed"
    );
}
