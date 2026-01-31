use crate::driver::artifact::CompilePhase;
use crate::intern::StringId;
use crate::lexer::*;
use crate::tests::test_utils;

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

#[cfg(test)]
mod tests {
    use super::*;

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

        for keyword in keywords {
            let symbol = StringId::new(keyword);
            let expected_kind =
                crate::lexer::is_keyword(symbol).unwrap_or_else(|| panic!("{} should be a keyword", keyword));

            let token_kinds = setup_lexer(keyword);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for keyword: {}", keyword);
            assert_eq!(token_kinds[0], expected_kind, "Failed for keyword: {}", keyword);
        }
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            ("+", TokenKind::Plus),
            ("-", TokenKind::Minus),
            ("*", TokenKind::Star),
            ("/", TokenKind::Slash),
            ("%", TokenKind::Percent),
            ("&", TokenKind::And),
            ("|", TokenKind::Or),
            ("^", TokenKind::Xor),
            ("!", TokenKind::Not),
            ("~", TokenKind::Tilde),
            ("<", TokenKind::Less),
            (">", TokenKind::Greater),
            ("<=", TokenKind::LessEqual),
            (">=", TokenKind::GreaterEqual),
            ("==", TokenKind::Equal),
            ("!=", TokenKind::NotEqual),
            ("<<", TokenKind::LeftShift),
            (">>", TokenKind::RightShift),
            ("=", TokenKind::Assign),
            ("+=", TokenKind::PlusAssign),
            ("-=", TokenKind::MinusAssign),
            ("*=", TokenKind::StarAssign),
            ("/=", TokenKind::DivAssign),
            ("%=", TokenKind::ModAssign),
            ("&=", TokenKind::AndAssign),
            ("|=", TokenKind::OrAssign),
            ("^=", TokenKind::XorAssign),
            ("<<=", TokenKind::LeftShiftAssign),
            (">>=", TokenKind::RightShiftAssign),
            ("++", TokenKind::Increment),
            ("--", TokenKind::Decrement),
            ("->", TokenKind::Arrow),
            (".", TokenKind::Dot),
            ("?", TokenKind::Question),
            (":", TokenKind::Colon),
            (",", TokenKind::Comma),
            (";", TokenKind::Semicolon),
            ("(", TokenKind::LeftParen),
            (")", TokenKind::RightParen),
            ("[", TokenKind::LeftBracket),
            ("]", TokenKind::RightBracket),
            ("{", TokenKind::LeftBrace),
            ("}", TokenKind::RightBrace),
            ("...", TokenKind::Ellipsis),
            ("&&", TokenKind::LogicAnd),
            ("||", TokenKind::LogicOr),
        ];

        for (text, expected_kind) in operators {
            let token_kinds = setup_lexer(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for operator: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for operator: {}", text);
        }
    }

    #[test]
    fn test_literals() {
        use crate::ast::literal::IntegerSuffix;
        // Integer constants
        let int_literals = vec![
            ("42", TokenKind::IntegerConstant(42, None)),
            ("0x1A", TokenKind::IntegerConstant(26, None)),
            ("077", TokenKind::IntegerConstant(63, None)),
            // C11 integer suffixes - decimal
            ("1ll", TokenKind::IntegerConstant(1, Some(IntegerSuffix::LL))),
            ("42u", TokenKind::IntegerConstant(42, Some(IntegerSuffix::U))),
            ("123l", TokenKind::IntegerConstant(123, Some(IntegerSuffix::L))),
            ("456ul", TokenKind::IntegerConstant(456, Some(IntegerSuffix::UL))),
            ("789lu", TokenKind::IntegerConstant(789, Some(IntegerSuffix::UL))),
            ("1000ull", TokenKind::IntegerConstant(1000, Some(IntegerSuffix::ULL))),
            ("2000llu", TokenKind::IntegerConstant(2000, Some(IntegerSuffix::ULL))),
            // C11 integer suffixes - hexadecimal
            ("0x1Au", TokenKind::IntegerConstant(26, Some(IntegerSuffix::U))),
            ("0xFFll", TokenKind::IntegerConstant(255, Some(IntegerSuffix::LL))),
            ("0x10UL", TokenKind::IntegerConstant(16, Some(IntegerSuffix::UL))),
            ("0x20LU", TokenKind::IntegerConstant(32, Some(IntegerSuffix::UL))),
            ("0x40ULL", TokenKind::IntegerConstant(64, Some(IntegerSuffix::ULL))),
            ("0x80LLU", TokenKind::IntegerConstant(128, Some(IntegerSuffix::ULL))),
            // C11 integer suffixes - octal
            ("077u", TokenKind::IntegerConstant(63, Some(IntegerSuffix::U))),
            ("0123l", TokenKind::IntegerConstant(83, Some(IntegerSuffix::L))),
            ("0777ul", TokenKind::IntegerConstant(511, Some(IntegerSuffix::UL))),
            ("0123lu", TokenKind::IntegerConstant(83, Some(IntegerSuffix::UL))),
            ("0777ull", TokenKind::IntegerConstant(511, Some(IntegerSuffix::ULL))),
            ("0123llu", TokenKind::IntegerConstant(83, Some(IntegerSuffix::ULL))),
            // Case insensitive suffixes
            ("1LL", TokenKind::IntegerConstant(1, Some(IntegerSuffix::LL))),
            ("42U", TokenKind::IntegerConstant(42, Some(IntegerSuffix::U))),
            ("123L", TokenKind::IntegerConstant(123, Some(IntegerSuffix::L))),
            ("456UL", TokenKind::IntegerConstant(456, Some(IntegerSuffix::UL))),
            ("789LU", TokenKind::IntegerConstant(789, Some(IntegerSuffix::UL))),
            ("1000ULL", TokenKind::IntegerConstant(1000, Some(IntegerSuffix::ULL))),
            ("2000LLU", TokenKind::IntegerConstant(2000, Some(IntegerSuffix::ULL))),
        ];

        for (text, expected_kind) in int_literals {
            let token_kinds = setup_lexer(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for integer literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for integer literal: {}", text);
        }

        // Float constants
        let float_literals = vec![
            // ⚡ Bolt: Improved coverage for hex float literals
            ("1.5", TokenKind::FloatConstant(1.5, None)),
            ("1.23e-4", TokenKind::FloatConstant(1.23e-4, None)),
            ("0x1.2p3", TokenKind::FloatConstant(9.0, None)),
        ];

        for (text, expected_kind) in float_literals {
            let token_kinds = setup_lexer(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for float literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for float literal: {}", text);
        }

        // Character constants
        let char_literals = vec![
            ("'a'", TokenKind::CharacterConstant(97)),   // 'a' = 97
            ("'\\n'", TokenKind::CharacterConstant(10)), // '\n' = 10
        ];

        for (text, expected_kind) in char_literals {
            let token_kinds = setup_lexer(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for character literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for character literal: {}", text);
        }

        // String literals
        let string_literals = vec![
            ("\"hello\"", TokenKind::StringLiteral(StringId::new("hello"))),
            ("\"world\\n\"", TokenKind::StringLiteral(StringId::new("world\n"))),
        ];

        for (text, expected_kind) in string_literals {
            let token_kinds = setup_lexer(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for string literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for string literal: {}", text);
        }
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        for ident in identifiers {
            let symbol = StringId::new(ident);
            let token_kinds = setup_lexer(ident);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for identifier: {}", ident);
            assert_eq!(
                token_kinds[0],
                TokenKind::Identifier(symbol),
                "Failed for identifier: {}",
                ident
            );
        }
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
                }
                _ => panic!("Expected StringLiteral token for input: {}", input),
            }
        }

        // Test that non-adjacent strings are not concatenated
        let token_kinds = setup_lexer("\"hello\" ; \"world\"");
        assert_eq!(token_kinds.len(), 3, "Expected 3 tokens for non-adjacent strings");
        assert!(
            matches!(token_kinds[0], TokenKind::StringLiteral(_)),
            "First token should be string literal"
        );
        assert_eq!(token_kinds[1], TokenKind::Semicolon, "Second token should be semicolon");
        assert!(
            matches!(token_kinds[2], TokenKind::StringLiteral(_)),
            "Third token should be string literal"
        );
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let token_kinds = setup_lexer_with_eof("", true);
        assert_eq!(token_kinds.len(), 1, "Expected 1 token for empty string");
        assert_eq!(
            token_kinds[0],
            TokenKind::EndOfFile,
            "Empty string should produce EndOfFile"
        );

        // Unknown - unrecognized character should produce Unknown
        let token_kinds = setup_lexer("@");
        assert_eq!(token_kinds.len(), 1, "Expected 1 token for unknown character");
        assert_eq!(
            token_kinds[0],
            TokenKind::Unknown,
            "Unrecognized character should produce Unknown"
        );
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

        for (input, expected) in test_cases {
            let token_kinds = setup_lexer(input);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for input: {}", input);

            if let TokenKind::StringLiteral(sid) = token_kinds[0] {
                assert_eq!(sid.as_str(), expected, "Failed for input: {}", input);
            } else {
                panic!("Expected StringLiteral for input: {}", input);
            }
        }
    }
}
