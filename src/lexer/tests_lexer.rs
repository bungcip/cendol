use super::*;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{SourceId, SourceLoc, SourceManager};
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple;

fn create_test_lexer(tokens: Vec<PPToken>) -> Lexer<'static> {
    let mut source_manager = SourceManager::new();
    let _source_id = source_manager.add_buffer("test".as_bytes().to_vec(), "test.c");
    let diag = DiagnosticEngine::new();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::host();

    Lexer::new(
        Box::leak(Box::new(source_manager)),
        Box::leak(Box::new(diag)),
        Box::leak(Box::new(lang_opts)),
        Box::leak(Box::new(target_info)),
        Box::leak(tokens.into_boxed_slice()),
    )
}

fn create_pptoken(kind: PPTokenKind, text: &str, offset: u32) -> PPToken {
    use std::num::NonZeroU32;
    PPToken::new(
        kind,
        PPTokenFlags::empty(),
        SourceLoc::new(SourceId(NonZeroU32::new(1).unwrap()), offset),
        text.len() as u16,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c11_keywords() {
        // Test all C11 keywords including C11-specific ones
        let keywords = vec![
            ("auto", TokenKind::Auto),
            ("break", TokenKind::Break),
            ("case", TokenKind::Case),
            ("char", TokenKind::Char),
            ("const", TokenKind::Const),
            ("continue", TokenKind::Continue),
            ("default", TokenKind::Default),
            ("do", TokenKind::Do),
            ("double", TokenKind::Double),
            ("else", TokenKind::Else),
            ("enum", TokenKind::Enum),
            ("extern", TokenKind::Extern),
            ("float", TokenKind::Float),
            ("for", TokenKind::For),
            ("goto", TokenKind::Goto),
            ("if", TokenKind::If),
            ("inline", TokenKind::Inline),
            ("int", TokenKind::Int),
            ("long", TokenKind::Long),
            ("register", TokenKind::Register),
            ("restrict", TokenKind::Restrict),
            ("return", TokenKind::Return),
            ("short", TokenKind::Short),
            ("signed", TokenKind::Signed),
            ("sizeof", TokenKind::Sizeof),
            ("static", TokenKind::Static),
            ("struct", TokenKind::Struct),
            ("switch", TokenKind::Switch),
            ("typedef", TokenKind::Typedef),
            ("union", TokenKind::Union),
            ("unsigned", TokenKind::Unsigned),
            ("void", TokenKind::Void),
            ("volatile", TokenKind::Volatile),
            ("while", TokenKind::While),
            // C11 specific keywords
            ("_Alignas", TokenKind::Alignas),
            ("_Alignof", TokenKind::Alignof),
            ("_Atomic", TokenKind::Atomic),
            ("_Bool", TokenKind::Bool),
            ("_Complex", TokenKind::Complex),
            ("_Generic", TokenKind::Generic),
            ("_Noreturn", TokenKind::Noreturn),
            ("_Pragma", TokenKind::Pragma),
            ("_Static_assert", TokenKind::StaticAssert),
            ("_Thread_local", TokenKind::ThreadLocal),
        ];

        for (text, expected_kind) in keywords {
            let symbol = Symbol::new(text);
            let pptoken = create_pptoken(PPTokenKind::Identifier(symbol), text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens[0].kind, expected_kind);
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
            let _pptoken = create_pptoken(PPTokenKind::Unknown, text, 0); // Using Unknown as placeholder, but classify_token will map it
            // Actually, I need to create PPTokens with the correct PPTokenKind
            // For simplicity, let's map the text to PPTokenKind
            let pp_kind = match text {
                "+" => PPTokenKind::Plus,
                "-" => PPTokenKind::Minus,
                "*" => PPTokenKind::Star,
                "/" => PPTokenKind::Slash,
                "%" => PPTokenKind::Percent,
                "&" => PPTokenKind::And,
                "|" => PPTokenKind::Or,
                "^" => PPTokenKind::Xor,
                "!" => PPTokenKind::Not,
                "~" => PPTokenKind::Tilde,
                "<" => PPTokenKind::Less,
                ">" => PPTokenKind::Greater,
                "<=" => PPTokenKind::LessEqual,
                ">=" => PPTokenKind::GreaterEqual,
                "==" => PPTokenKind::Equal,
                "!=" => PPTokenKind::NotEqual,
                "<<" => PPTokenKind::LeftShift,
                ">>" => PPTokenKind::RightShift,
                "=" => PPTokenKind::Assign,
                "+=" => PPTokenKind::PlusAssign,
                "-=" => PPTokenKind::MinusAssign,
                "*=" => PPTokenKind::StarAssign,
                "/=" => PPTokenKind::DivAssign,
                "%=" => PPTokenKind::ModAssign,
                "&=" => PPTokenKind::AndAssign,
                "|=" => PPTokenKind::OrAssign,
                "^=" => PPTokenKind::XorAssign,
                "<<=" => PPTokenKind::LeftShiftAssign,
                ">>=" => PPTokenKind::RightShiftAssign,
                "++" => PPTokenKind::Increment,
                "--" => PPTokenKind::Decrement,
                "->" => PPTokenKind::Arrow,
                "." => PPTokenKind::Dot,
                "?" => PPTokenKind::Question,
                ":" => PPTokenKind::Colon,
                "," => PPTokenKind::Comma,
                ";" => PPTokenKind::Semicolon,
                "(" => PPTokenKind::LeftParen,
                ")" => PPTokenKind::RightParen,
                "[" => PPTokenKind::LeftBracket,
                "]" => PPTokenKind::RightBracket,
                "{" => PPTokenKind::LeftBrace,
                "}" => PPTokenKind::RightBrace,
                "..." => PPTokenKind::Ellipsis,
                "&&" => PPTokenKind::LogicAnd,
                "||" => PPTokenKind::LogicOr,
                _ => panic!("Unknown operator: {}", text),
            };
            let pptoken = create_pptoken(pp_kind, text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1, "Failed for operator: {}", text);
            assert_eq!(
                tokens[0].kind, expected_kind,
                "Failed for operator: {}",
                text
            );
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
            let symbol = Symbol::new(text);
            let pptoken = create_pptoken(PPTokenKind::Number(symbol), text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens[0].kind, expected_kind);
        }

        // Float constants - treated as FloatConstant since classify_token maps Number to FloatConstant if integer parsing fails
        let float_literals = vec![
            ("3.14", TokenKind::FloatConstant(Symbol::new("3.14"))),
            ("1.23e-4", TokenKind::FloatConstant(Symbol::new("1.23e-4"))),
        ];

        for (text, expected_kind) in float_literals {
            let symbol = Symbol::new(text);
            let pptoken = create_pptoken(PPTokenKind::Number(symbol), text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens[0].kind, expected_kind);
        }

        // Character constants
        let char_literals = vec![
            ("'a'", 97u32),   // 'a' = 97
            ("'\\n'", 10u32), // '\n' = 10
        ];

        for (text, expected_codepoint) in char_literals {
            let pptoken = create_pptoken(PPTokenKind::CharLiteral(expected_codepoint), text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(
                tokens[0].kind,
                TokenKind::CharacterConstant(expected_codepoint)
            );
        }

        // String literals
        let string_literals = vec![
            (
                "\"hello\"",
                TokenKind::StringLiteral(Symbol::new("\"hello\"")),
            ),
            (
                "\"world\\n\"",
                TokenKind::StringLiteral(Symbol::new("\"world\\n\"")),
            ),
        ];

        for (text, expected_kind) in string_literals {
            let symbol = Symbol::new(text);
            let pptoken = create_pptoken(PPTokenKind::StringLiteral(symbol), text, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens[0].kind, expected_kind);
        }
    }

    #[test]
    fn test_identifiers() {
        let identifiers = vec!["variable", "my_var", "_private", "var123", "a", "_"];

        for ident in identifiers {
            let symbol = Symbol::new(ident);
            let pptoken = create_pptoken(PPTokenKind::Identifier(symbol), ident, 0);
            let mut lexer = create_test_lexer(vec![pptoken]);

            let tokens = lexer.tokenize_all();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens[0].kind, TokenKind::Identifier(symbol));
        }
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile
        let eof_pptoken = create_pptoken(PPTokenKind::Eof, "", 0);
        let mut lexer = create_test_lexer(vec![eof_pptoken]);

        let tokens = lexer.tokenize_all();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::EndOfFile);

        // Unknown
        let unknown_pptoken = create_pptoken(PPTokenKind::Unknown, "@", 0);
        let mut lexer = create_test_lexer(vec![unknown_pptoken]);

        let tokens = lexer.tokenize_all();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::Unknown);
    }
}
