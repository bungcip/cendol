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

/// Helper function to batch process lexer inputs for snapshot testing
fn setup_lexer_snapshot(inputs: Vec<&str>) -> Vec<(&str, Vec<TokenKind>)> {
    inputs
        .into_iter()
        .map(|input| (input, setup_lexer(input)))
        .collect()
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

        let results = setup_lexer_snapshot(keywords);
        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            "+", "-", "*", "/", "%", "&", "|", "^", "!", "~", "<", ">", "<=", ">=", "==", "!=",
            "<<", ">>", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
            "++", "--", "->", ".", "?", ":", ",", ";", "(", ")", "[", "]", "{", "}", "...",
            "&&", "||",
        ];

        let results = setup_lexer_snapshot(operators);
        insta::assert_yaml_snapshot!(results);
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
        let float_literals = vec!["1.5", "1.23e-4", "0x1.2p3"];

        // Character constants
        let char_literals = vec!["'a'", "'\\n'"];

        // String literals
        let string_literals = vec!["\"hello\"", "\"world\\n\""];

        let mut results = Vec::new();
        results.push(("Integers", setup_lexer_snapshot(int_literals)));
        results.push(("Floats", setup_lexer_snapshot(float_literals)));
        results.push(("Chars", setup_lexer_snapshot(char_literals)));
        results.push(("Strings", setup_lexer_snapshot(string_literals)));

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];
        let results = setup_lexer_snapshot(identifiers);
        insta::assert_yaml_snapshot!(results);
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

        let results = setup_lexer_snapshot(test_cases);
        insta::assert_yaml_snapshot!(results);

        // Test that non-adjacent strings are not concatenated
        let non_adjacent = setup_lexer("\"hello\" ; \"world\"");
        insta::assert_yaml_snapshot!(non_adjacent);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let empty_tokens = setup_lexer_with_eof("", true);

        // Unknown - unrecognized character should produce Unknown
        let unknown_tokens = setup_lexer("@");

        insta::assert_yaml_snapshot!((empty_tokens, unknown_tokens));
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

        let results = setup_lexer_snapshot(test_cases);
        insta::assert_yaml_snapshot!(results);
    }
}
