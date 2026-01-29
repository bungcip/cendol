use crate::driver::artifact::CompilePhase;
use crate::lexer::*;
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

        let results: BTreeMap<_, _> = keywords
            .iter()
            .map(|keyword| (*keyword, setup_lexer(keyword)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            "+", "-", "*", "/", "%", "&", "|", "^", "!", "~", "<", ">", "<=", ">=", "==", "!=",
            "<<", ">>", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++",
            "--", "->", ".", "?", ":", ",", ";", "(", ")", "[", "]", "{", "}", "...", "&&", "||",
        ];

        // Map to just text for the snapshot key to keep it clean
        let results: BTreeMap<_, _> = operators
            .iter()
            .map(|op| (*op, setup_lexer(op)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_literals() {
        // Integer constants
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

        let results: BTreeMap<_, _> = int_literals
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!("integer_literals", results);

        // Float constants
        let float_literals = vec![
            "1.5",
            "1.23e-4",
            "0x1.2p3",
        ];

        let results: BTreeMap<_, _> = float_literals
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!("float_literals", results);

        // Character constants
        let char_literals = vec![
            "'a'",
            "'\\n'",
        ];

        let results: BTreeMap<_, _> = char_literals
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!("char_literals", results);

        // String literals
        let string_literals = vec![
            "\"hello\"",
            "\"world\\n\"",
        ];

        let results: BTreeMap<_, _> = string_literals
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!("string_literals", results);
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        let results: BTreeMap<_, _> = identifiers
            .iter()
            .map(|ident| (*ident, setup_lexer(ident)))
            .collect();

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

        let results: BTreeMap<_, _> = test_cases
            .iter()
            .map(|input| (*input, setup_lexer(input)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_non_adjacent_string_literals() {
         let input = "\"hello\" ; \"world\"";
         let tokens = setup_lexer(input);
         insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let eof_tokens = setup_lexer_with_eof("", true);
        insta::assert_yaml_snapshot!("eof_token", eof_tokens);

        // Unknown - unrecognized character should produce Unknown
        let unknown_tokens = setup_lexer("@");
        insta::assert_yaml_snapshot!("unknown_token", unknown_tokens);
    }

    #[test]
    fn test_complex_float_literals() {
        let cases = vec![
            "0x1.fp-2",
            "0x.p0",     // Invalid hex float (must have digits) - wait, C11 says hex float must have digits
                         // actually 0x.p0 is invalid because hex-float requires hex digits either before or after dot.
                         // But `.` alone is not a valid hex float prefix.
            "0x.8p0",    // Valid
            "0x1p+5",    // Valid
            "1.f",       // Valid float with suffix
            ".5f",       // Valid
            "1e5f",      // Valid
            "0x1P-1L",   // Valid hex float with long double suffix
        ];

        let results: BTreeMap<_, _> = cases
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_complex_integer_suffixes() {
        let cases = vec![
            "1uLl", // Valid: unsigned long long (mixed case)
            "1UlL", // Valid: unsigned long long
            "1LLu", // Valid: long long unsigned
            "1llU", // Valid
            "1Lu",  // Valid: long unsigned
            "1uL",  // Valid
            // Invalid ones are usually handled by parser or lexer error, here we check what token we get.
            // If lexer is robust, it might consume valid prefix.
        ];

        let results: BTreeMap<_, _> = cases
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }

    #[test]
    fn test_string_escapes() {
        let cases = vec![
            r#""\x41""#,      // Hex 'A'
            r#""\101""#,      // Octal 'A'
            r#""\?""#,        // Question mark
            r#""\"""#,        // Double quote
            r#""\'""#,        // Single quote
            r#""\a\b\f\n\r\t\v""#, // Common escapes
            r#""\x""#,        // Empty hex escape (invalid but interesting to see lexer behavior)
            r#""\777""#,      // Octal overflow (char is u8, so it wraps or errors?)
        ];

        let results: BTreeMap<_, _> = cases
            .iter()
            .map(|lit| (*lit, setup_lexer(lit)))
            .collect();

        insta::assert_yaml_snapshot!(results);
    }
}
