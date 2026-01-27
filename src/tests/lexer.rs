use crate::driver::artifact::CompilePhase;
use crate::lexer::*;
use crate::tests::test_utils;
use serde::Serialize;

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

#[derive(Serialize)]
enum SnapshotTokenKind {
    IntegerConstant(i64),
    FloatConstant(f64),
    CharacterConstant(u8),
    StringLiteral(String),
    Identifier(String),
    #[serde(untagged)]
    Other(String),
}

impl From<TokenKind> for SnapshotTokenKind {
    fn from(kind: TokenKind) -> Self {
        match kind {
            TokenKind::IntegerConstant(v) => SnapshotTokenKind::IntegerConstant(v),
            TokenKind::FloatConstant(v) => SnapshotTokenKind::FloatConstant(v),
            TokenKind::CharacterConstant(v) => SnapshotTokenKind::CharacterConstant(v),
            TokenKind::StringLiteral(id) => SnapshotTokenKind::StringLiteral(id.as_str().to_string()),
            TokenKind::Identifier(id) => SnapshotTokenKind::Identifier(id.as_str().to_string()),
            other => SnapshotTokenKind::Other(format!("{:?}", other)),
        }
    }
}

fn setup_lexer_snapshot(input: &str) -> Vec<SnapshotTokenKind> {
    setup_lexer(input).into_iter().map(Into::into).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c11_keywords() {
        #[rustfmt::skip]
        let keywords = vec![
            "auto", "break", "case", "char", "const", "continue", "default", "do",
            "double", "else", "enum", "extern", "float", "for", "goto", "if",
            "inline", "int", "long", "register", "restrict", "return", "short",
            "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
            "unsigned", "void", "volatile", "while",
            "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic",
            "_Noreturn", "_Static_assert", "_Thread_local",
        ];

        // Combine all keywords into one string to test them all at once
        let source = keywords.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_operators_and_punctuation() {
        let operators = vec![
            "+", "-", "*", "/", "%", "&", "|", "^", "!", "~", "<", ">", "<=", ">=", "==", "!=",
            "<<", ">>", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++",
            "--", "->", ".", "?", ":", ",", ";", "(", ")", "[", "]", "{", "}", "...", "&&", "||",
        ];

        let source = operators.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_literals() {
        // Integer constants
        let int_literals = vec![
            "42",
            "0x1A",
            "077",
            "1ll",
            "42u",
            "123l",
            "456ul",
            "789lu",
            "1000ull",
            "2000llu",
            "0x1Au",
            "0xFFll",
            "0x10UL",
            "0x20LU",
            "0x40ULL",
            "0x80LLU",
            "077u",
            "0123l",
            "0777ul",
            "0123lu",
            "0777ull",
            "0123llu",
            "1LL",
            "42U",
            "123L",
            "456UL",
            "789LU",
            "1000ULL",
            "2000LLU",
        ];

        let source = int_literals.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_float_literals() {
        let float_literals = vec![
            "1.5",
            "1.23e-4",
            "0x1.2p3",
            // Hex floats variants
            "0x1p+1",
            "0x1.fp-2",
            "0x1P+1",
        ];

        let source = float_literals.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_char_literals() {
        let char_literals = vec![
            "'a'",
            "'\\n'",
        ];

        let source = char_literals.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_string_literals() {
        let string_literals = vec![
            "\"hello\"",
            "\"world\\n\"",
        ];

        let source = string_literals.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        let source = identifiers.join(" ");
        let tokens = setup_lexer_snapshot(&source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_string_literal_concatenation() {
        let test_cases = vec![
            "\"hello\" \"world\"",
            "\"hello\"   \"world\"",
            "\"a\" \"b\" \"c\"",
            "\"hello\\n\" \"world\"",
            "\"start\" \" middle \" \"end\"",
        ];

        for input in test_cases {
            let tokens = setup_lexer_snapshot(input);
            insta::assert_yaml_snapshot!(tokens);
        }
    }

    #[test]
    fn test_non_concatenation() {
        // Test that non-adjacent strings are not concatenated
        let input = "\"hello\" ; \"world\"";
        let tokens = setup_lexer_snapshot(input);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile
        let tokens = setup_lexer_with_eof("", true)
            .into_iter()
            .map(Into::into)
            .collect::<Vec<SnapshotTokenKind>>();
        insta::assert_yaml_snapshot!(tokens);

        // Unknown
        let tokens = setup_lexer_snapshot("@");
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_comments() {
        let source = r#"
            // Line comment
            int x = 1; /* Block
            Comment */
            int y = 2;
        "#;
        let tokens = setup_lexer_snapshot(source);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_complex_escapes() {
        // Hex and octal escapes in strings
        let source = r#""\x41\x42" "\101\102""#; // "AB" "AB"
        let tokens = setup_lexer_snapshot(source);
        insta::assert_yaml_snapshot!(tokens);
    }
}
