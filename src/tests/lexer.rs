use crate::driver::artifact::CompilePhase;
use crate::lexer::*;
use crate::tests::test_utils;
use insta::assert_yaml_snapshot;

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

        let mut all_tokens = Vec::new();
        for keyword in keywords {
            all_tokens.extend(setup_lexer(keyword));
        }

        assert_yaml_snapshot!(all_tokens);
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            "+", "-", "*", "/", "%", "&", "|", "^", "!", "~",
            "<", ">", "<=", ">=", "==", "!=",
            "<<", ">>", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
            "++", "--", "->", ".", "?", ":", ",", ";",
            "(", ")", "[", "]", "{", "}", "...", "&&", "||",
        ];

        let mut all_tokens = Vec::new();
        for op in operators {
            all_tokens.extend(setup_lexer(op));
        }

        assert_yaml_snapshot!(all_tokens);
    }

    #[test]
    fn test_literals() {
        // Integer constants
        let int_literals = vec![
            "42", "0x1A", "077",
            "1ll", "42u", "123l", "456ul", "789lu", "1000ull", "2000llu",
            "0x1Au", "0xFFll", "0x10UL", "0x20LU", "0x40ULL", "0x80LLU",
            "077u", "0123l", "0777ul", "0123lu", "0777ull", "0123llu",
            "1LL", "42U", "123L", "456UL", "789LU", "1000ULL", "2000LLU",
        ];

        let mut int_tokens = Vec::new();
        for lit in int_literals {
             int_tokens.push(setup_lexer(lit));
        }
        assert_yaml_snapshot!("integer_literals", int_tokens);

        // Float constants
        let float_literals = vec![
            "1.5", "1.23e-4", "0x1.2p3",
        ];

        let mut float_tokens = Vec::new();
        for lit in float_literals {
             float_tokens.push(setup_lexer(lit));
        }
        assert_yaml_snapshot!("float_literals", float_tokens);

        // Character constants
        let char_literals = vec![
            "'a'", "'\\n'",
        ];

        let mut char_tokens = Vec::new();
        for lit in char_literals {
             char_tokens.push(setup_lexer(lit));
        }
        assert_yaml_snapshot!("char_literals", char_tokens);

        // String literals
        let string_literals = vec![
            "\"hello\"", "\"world\\n\"",
        ];

        let mut string_tokens = Vec::new();
        for lit in string_literals {
             string_tokens.push(setup_lexer(lit));
        }
        assert_yaml_snapshot!("string_literals", string_tokens);
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        let mut ident_tokens = Vec::new();
        for ident in identifiers {
            ident_tokens.push(setup_lexer(ident));
        }

        assert_yaml_snapshot!(ident_tokens);
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

        let mut tokens = Vec::new();
        for case in test_cases {
            tokens.push(setup_lexer(case));
        }
        assert_yaml_snapshot!(tokens);

        // Test that non-adjacent strings are not concatenated
        let non_adjacent = setup_lexer("\"hello\" ; \"world\"");
        assert_yaml_snapshot!("non_adjacent_strings", non_adjacent);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let eof_token = setup_lexer_with_eof("", true);
        assert_yaml_snapshot!("eof_token", eof_token);

        // Unknown - unrecognized character should produce Unknown
        let unknown_token = setup_lexer("@");
        assert_yaml_snapshot!("unknown_token", unknown_token);
    }
}
