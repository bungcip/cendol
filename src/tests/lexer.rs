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

/// Helper to run lexer on multiple cases and collect results for snapshotting
fn snapshot_lexer_cases(cases: Vec<&str>) -> Vec<(&str, Vec<TokenKind>)> {
    cases
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

        insta::assert_yaml_snapshot!(snapshot_lexer_cases(keywords));
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            "+", "-", "*", "/", "%", "&", "|", "^", "!", "~", "<", ">", "<=", ">=", "==", "!=",
            "<<", ">>", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++",
            "--", "->", ".", "?", ":", ",", ";", "(", ")", "[", "]", "{", "}", "...", "&&", "||",
        ];

        insta::assert_yaml_snapshot!(snapshot_lexer_cases(operators));
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

        let mut cases = int_literals;
        cases.extend(float_literals);
        cases.extend(char_literals);
        cases.extend(string_literals);

        insta::assert_yaml_snapshot!(snapshot_lexer_cases(cases));
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        insta::assert_yaml_snapshot!(snapshot_lexer_cases(identifiers));
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
            // Non-adjacent (should not concatenate)
            "\"hello\" ; \"world\"",
        ];

        insta::assert_yaml_snapshot!(snapshot_lexer_cases(test_cases));
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let eof = setup_lexer_with_eof("", true);

        // Unknown - unrecognized character should produce Unknown
        let unknown = setup_lexer("@");

        insta::assert_yaml_snapshot!((eof, unknown));
    }
}
