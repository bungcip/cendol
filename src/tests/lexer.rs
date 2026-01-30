use crate::driver::artifact::CompilePhase;
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

        // Create a single string with all keywords separated by spaces
        let input = keywords.join(" ");
        let token_kinds = setup_lexer(&input);

        insta::assert_yaml_snapshot!(token_kinds);
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
            ",", ";",
            "(", ")", "[", "]", "{", "}",
            "...",
            "&&", "||",
        ];

        // Join with spaces to avoid accidental merging (e.g. + + becoming ++)
        let input = operators.join(" ");
        let token_kinds = setup_lexer(&input);

        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_integer_literals() {
        let int_literals = vec![
            "42",
            "0x1A",
            "077",
            // C11 integer suffixes - decimal
            "1ll",
            "42u",
            "123l",
            "456ul",
            "789lu",
            "1000ull",
            "2000llu",
            // C11 integer suffixes - hexadecimal
            "0x1Au",
            "0xFFll",
            "0x10UL",
            "0x20LU",
            "0x40ULL",
            "0x80LLU",
            // C11 integer suffixes - octal
            "077u",
            "0123l",
            "0777ul",
            "0123lu",
            "0777ull",
            "0123llu",
            // Case insensitive suffixes
            "1LL",
            "42U",
            "123L",
            "456UL",
            "789LU",
            "1000ULL",
            "2000LLU",
        ];

        let input = int_literals.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_float_literals() {
        let float_literals = vec![
            "1.5",
            "1.23e-4",
            "0x1.2p3",
        ];

        let input = float_literals.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_char_literals() {
        let char_literals = vec![
            "'a'",
            "'\\n'",
        ];

        let input = char_literals.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_string_literals() {
        let string_literals = vec![
            "\"hello\"",
            "\"world\\n\"",
        ];

        // Join with semicolon to prevent string concatenation
        let input = string_literals.join("; ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        let input = identifiers.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_string_literal_concatenation() {
        // Test adjacent string literal concatenation (C11 6.4.5)
        let test_cases = vec![
            // Basic concatenation
            "\"hello\" \"world\"",
            // With whitespace between
            "\"hello\"   \"world\"",
            // Multiple concatenations
            "\"a\" \"b\" \"c\"",
            // With escape sequences
            "\"hello\\n\" \"world\"",
            // Mixed quotes and content
            "\"start\" \" middle \" \"end\"",
        ];

        // For concatenation tests, we test each case individually to verify
        // they merge into a single token.
        for (i, input) in test_cases.iter().enumerate() {
            let token_kinds = setup_lexer(input);
            insta::assert_yaml_snapshot!(format!("concatenation_{}", i), token_kinds);
        }

        // Test that non-adjacent strings are not concatenated
        let input = "\"hello\" ; \"world\"";
        let token_kinds = setup_lexer(input);
        insta::assert_yaml_snapshot!("non_adjacent", token_kinds);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let token_kinds_eof = setup_lexer_with_eof("", true);
        insta::assert_yaml_snapshot!("eof", token_kinds_eof);

        // Unknown - unrecognized character should produce Unknown
        let token_kinds_unknown = setup_lexer("@");
        insta::assert_yaml_snapshot!("unknown", token_kinds_unknown);
    }

    #[test]
    fn test_string_escapes_edge_cases() {
        // Test edge cases in string literal unescaping
        let test_cases = vec![
            // \x with no digits - should keep the x
            "\"\\xg\"",
            // \x with invalid unicode value (overflow) - should use replacement character
            // \x110000 is > 0x10FFFF
            "\"\\x110000\"",
            // \? escape
            "\"\\?\"",
            // Unknown escape sequence (e.g. \q) - should keep the character
            "\"\\q\"",
        ];

        for (i, input) in test_cases.iter().enumerate() {
            let token_kinds = setup_lexer(input);
            insta::assert_yaml_snapshot!(format!("escape_{}", i), token_kinds);
        }
    }

    // === NEW TESTS ===

    #[test]
    fn test_complex_float_literals() {
        let test_cases = vec![
            // Hexadecimal floats (C11)
            "0x1p+1",
            "0x1.fp-2",
            "0x1P+1",
            "0x.8p0",

            // Suffixes
            "1.0f",
            "1.0F",
            "1.0l",
            "1.0L",
            "0x1p1f",
            "0x1p1L",

            // Edge cases
            "1.",  // Valid
            ".5",  // Valid (but note existing memory says this might be misparsed?)
            "1.e2", // Valid
        ];

        let input = test_cases.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_complex_integer_suffixes() {
        let test_cases = vec![
            // Unsigned
            "1u", "1U",
            // Long
            "1l", "1L",
            // Long Long
            "1ll", "1LL",
            // Unsigned Long
            "1ul", "1uL", "1Ul", "1UL",
            "1lu", "1lU", "1Lu", "1LU",
            // Unsigned Long Long
            "1ull", "1uLL", "1Ull", "1ULL",
            "1llu", "1llU", "1LLu", "1LLU",

            // Hex
            "0x1u", "0x1L", "0x1llU",

            // Octal
            "01u", "01L", "01llU",
        ];

        let input = test_cases.join(" ");
        let token_kinds = setup_lexer(&input);
        insta::assert_yaml_snapshot!(token_kinds);
    }

    #[test]
    fn test_string_escapes() {
        let test_cases = vec![
            "\"Standard: \\' \\\" \\? \\\\ \\a \\b \\f \\n \\r \\t \\v\"",
            "\"Octal: \\1 \\12 \\123\"",
            "\"Hex: \\x1 \\x12 \\x123\"", // Note: hex escape consumes all following hex digits
            "\"Universal: \\u0041 \\U00000041\"", // A
        ];

        for (i, input) in test_cases.iter().enumerate() {
            let token_kinds = setup_lexer(input);
            insta::assert_yaml_snapshot!(format!("string_escapes_{}", i), token_kinds);
        }
    }
}
