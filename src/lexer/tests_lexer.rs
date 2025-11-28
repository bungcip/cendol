use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::pp::{Preprocessor, PPConfig};
use crate::source_manager::SourceManager;
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple;


/// Helper function to test lexing from string to TokenKind
/// This tests the full pipeline: string -> PPToken -> TokenKind
fn lex_string_to_token_kind(input: &str) -> Vec<TokenKind> {
    lex_string_to_token_kind_with_eof(input, false)
}

/// Helper function to test lexing from string to TokenKind, optionally including EndOfFile
fn lex_string_to_token_kind_with_eof(input: &str, include_eof: bool) -> Vec<TokenKind> {
    let mut source_manager = SourceManager::new();
    let source_id = source_manager.add_buffer(input.as_bytes().to_vec(), "test_input");
    let mut diag = DiagnosticEngine::new();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::host();

    let pp_config = PPConfig {
        max_include_depth: 10,
        ..Default::default()
    };

    let pp_tokens = {
        let mut preprocessor = Preprocessor::new(
            &mut source_manager,
            &mut diag,
            lang_opts.clone(),
            target_info.clone(),
            &pp_config,
        );
        preprocessor.process(source_id, &pp_config).unwrap()
    }; // preprocessor is dropped here

    let mut lexer = Lexer::new(
        &source_manager,
        &mut diag,
        &lang_opts,
        &target_info,
        &pp_tokens,
    );

    let tokens = lexer.tokenize_all();
    if include_eof {
        tokens.into_iter().map(|t| t.kind).collect()
    } else {
        tokens.into_iter()
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
            "_Noreturn", "_Pragma", "_Static_assert", "_Thread_local",
        ];

        let keyword_table = KeywordTable::new();

        for keyword in keywords {
            let symbol = Symbol::new(keyword);
            let expected_kind = keyword_table.is_keyword(symbol)
                .expect(&format!("{} should be a keyword", keyword));

            let token_kinds = lex_string_to_token_kind(keyword);
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
            let token_kinds = lex_string_to_token_kind(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for operator: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for operator: {}", text);
        }
    }

    #[test]
    fn test_literals() {
        // Integer constants
        let int_literals = vec![
            ("42", TokenKind::IntegerConstant(42)),
            ("0x1A", TokenKind::IntegerConstant(26)),
            ("077", TokenKind::IntegerConstant(63)),
        ];

        for (text, expected_kind) in int_literals {
            let token_kinds = lex_string_to_token_kind(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for integer literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for integer literal: {}", text);
        }

        // Float constants - treated as FloatConstant since classify_token maps Number to FloatConstant if integer parsing fails
        let float_literals = vec![
            ("3.14", TokenKind::FloatConstant(Symbol::new("3.14"))),
            ("1.23e-4", TokenKind::FloatConstant(Symbol::new("1.23e-4"))),
        ];

        for (text, expected_kind) in float_literals {
            let token_kinds = lex_string_to_token_kind(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for float literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for float literal: {}", text);
        }

        // Character constants
        let char_literals = vec![
            ("'a'", TokenKind::CharacterConstant(97)),   // 'a' = 97
            ("'\\n'", TokenKind::CharacterConstant(10)), // '\n' = 10
        ];

        for (text, expected_kind) in char_literals {
            let token_kinds = lex_string_to_token_kind(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for character literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for character literal: {}", text);
        }

        // String literals
        let string_literals = vec![
            ("\"hello\"", TokenKind::StringLiteral(Symbol::new("\"hello\""))),
            ("\"world\\n\"", TokenKind::StringLiteral(Symbol::new("\"world\\n\""))),
        ];

        for (text, expected_kind) in string_literals {
            let token_kinds = lex_string_to_token_kind(text);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for string literal: {}", text);
            assert_eq!(token_kinds[0], expected_kind, "Failed for string literal: {}", text);
        }
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        for ident in identifiers {
            let symbol = Symbol::new(ident);
            let token_kinds = lex_string_to_token_kind(ident);
            assert_eq!(token_kinds.len(), 1, "Expected 1 token for identifier: {}", ident);
            assert_eq!(token_kinds[0], TokenKind::Identifier(symbol), "Failed for identifier: {}", ident);
        }
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile - empty string should produce EndOfFile when included
        let token_kinds = lex_string_to_token_kind_with_eof("", true);
        assert_eq!(token_kinds.len(), 1, "Expected 1 token for empty string");
        assert_eq!(token_kinds[0], TokenKind::EndOfFile, "Empty string should produce EndOfFile");

        // Unknown - unrecognized character should produce Unknown
        let token_kinds = lex_string_to_token_kind("@");
        assert_eq!(token_kinds.len(), 1, "Expected 1 token for unknown character");
        assert_eq!(token_kinds[0], TokenKind::Unknown, "Unrecognized character should produce Unknown");
    }
}
