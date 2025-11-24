use crate::preprocessor::{PPLexer, PPTokenFlags, PPTokenKind};
use crate::source_manager::{SourceId};
use symbol_table::GlobalSymbol as Symbol;
use std::num::NonZeroU32;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId(NonZeroU32::new(1).unwrap());
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test 1: Check if PPLexer can correctly lex source code to PPKind token for all punctuation
    #[test]
    fn test_punctuation_lexing() {
        let test_cases = vec![
            ("+", PPTokenKind::Plus),
            ("-", PPTokenKind::Minus),
            ("*", PPTokenKind::Star),
            ("/", PPTokenKind::Slash),
            ("%", PPTokenKind::Percent),
            ("&", PPTokenKind::And),
            ("|", PPTokenKind::Or),
            ("^", PPTokenKind::Xor),
            ("!", PPTokenKind::Not),
            ("~", PPTokenKind::Tilde),
            ("<", PPTokenKind::Less),
            (">", PPTokenKind::Greater),
            ("=", PPTokenKind::Assign),
            ("==", PPTokenKind::Equal),
            ("!=", PPTokenKind::NotEqual),
            ("<=", PPTokenKind::LessEqual),
            (">=", PPTokenKind::GreaterEqual),
            ("&&", PPTokenKind::LogicAnd),
            ("||", PPTokenKind::LogicOr),
            ("++", PPTokenKind::Increment),
            ("--", PPTokenKind::Decrement),
            ("->", PPTokenKind::Arrow),
            ("+=", PPTokenKind::PlusAssign),
            ("-=", PPTokenKind::MinusAssign),
            ("*=", PPTokenKind::StarAssign),
            ("/=", PPTokenKind::DivAssign),
            ("%=", PPTokenKind::ModAssign),
            ("&=", PPTokenKind::AndAssign),
            ("|=", PPTokenKind::OrAssign),
            ("^=", PPTokenKind::XorAssign),
            ("<<", PPTokenKind::LeftShift),
            (">>", PPTokenKind::RightShift),
            ("<<=", PPTokenKind::LeftShiftAssign),
            (">>=", PPTokenKind::RightShiftAssign),
            ("...", PPTokenKind::Ellipsis),
            ("#", PPTokenKind::Hash),
            ("##", PPTokenKind::HashHash),
            ("?", PPTokenKind::Question),
            (":", PPTokenKind::Colon),
            (",", PPTokenKind::Comma),
            (";", PPTokenKind::Semicolon),
            ("(", PPTokenKind::LeftParen),
            (")", PPTokenKind::RightParen),
            ("[", PPTokenKind::LeftBracket),
            ("]", PPTokenKind::RightBracket),
            ("{", PPTokenKind::LeftBrace),
            ("}", PPTokenKind::RightBrace),
            (".", PPTokenKind::Dot),
        ];

        for (source, expected_kind) in test_cases {
            let mut lexer = create_test_pp_lexer(source);
            let token = lexer.next_token();
            
            assert!(token.is_some(), "Failed to lex punctuation: {}", source);
            let actual_token = token.unwrap();
            
            assert_eq!(actual_token.kind, expected_kind,
                "Incorrect token kind for punctuation: {}", source);
            assert_eq!(actual_token.length as usize, source.len(),
                "Incorrect token length for punctuation: {}", source);
        }
    }

    /// Test 2: Check if PPLexer can produce directive tokens
    #[test]
    fn test_directive_tokens() {
        let test_cases = vec![
            ("#if", PPTokenKind::Hash, PPTokenKind::If),
            ("#ifdef", PPTokenKind::Hash, PPTokenKind::Ifdef),
            ("#ifndef", PPTokenKind::Hash, PPTokenKind::Ifndef),
            ("#elif", PPTokenKind::Hash, PPTokenKind::Elif),
            ("#else", PPTokenKind::Hash, PPTokenKind::Else),
            ("#endif", PPTokenKind::Hash, PPTokenKind::Endif),
            ("#define", PPTokenKind::Hash, PPTokenKind::Define),
            ("#undef", PPTokenKind::Hash, PPTokenKind::Undef),
            ("#include", PPTokenKind::Hash, PPTokenKind::Include),
            ("#line", PPTokenKind::Hash, PPTokenKind::Line),
            ("#pragma", PPTokenKind::Hash, PPTokenKind::Pragma),
            ("#error", PPTokenKind::Hash, PPTokenKind::Error),
            ("#warning", PPTokenKind::Hash, PPTokenKind::Warning),
        ];

        for (source, expected_first, expected_second) in test_cases {
            let mut lexer = create_test_pp_lexer(source);
            
            // Test first token (should be #)
            let first_token = lexer.next_token();
            assert!(first_token.is_some(), "Failed to lex directive: {}", source);
            let actual_first = first_token.unwrap();
            
            assert_eq!(actual_first.kind, expected_first,
                "Incorrect first token for directive: {}", source);
            assert!(actual_first.flags.contains(PPTokenFlags::STARTS_PP_LINE),
                "First token should have STARTS_PP_LINE flag");
            
            // Test second token (should be directive keyword)
            let second_token = lexer.next_token();
            assert!(second_token.is_some(), "Failed to lex directive keyword");
            let actual_second = second_token.unwrap();
            
            assert_eq!(actual_second.kind, expected_second,
                "Incorrect second token for directive: {}", source);
        }
    }

    /// Test 3: Check if PPLexer can produce keyword tokens
    #[test]
    fn test_keyword_tokens() {
        let test_cases = vec![
            ("if", PPTokenKind::If),
            ("ifdef", PPTokenKind::Ifdef),
            ("ifndef", PPTokenKind::Ifndef),
            ("elif", PPTokenKind::Elif),
            ("else", PPTokenKind::Else),
            ("endif", PPTokenKind::Endif),
            ("define", PPTokenKind::Define),
            ("undef", PPTokenKind::Undef),
            ("include", PPTokenKind::Include),
            ("line", PPTokenKind::Line),
            ("pragma", PPTokenKind::Pragma),
            ("error", PPTokenKind::Error),
            ("warning", PPTokenKind::Warning),
        ];

        for (source, expected_kind) in test_cases {
            let mut lexer = create_test_pp_lexer(source);
            let token = lexer.next_token();
            
            assert!(token.is_some(), "Failed to lex keyword: {}", source);
            let actual_token = token.unwrap();
            
            assert_eq!(actual_token.kind, expected_kind,
                "Incorrect token kind for keyword: {}", source);
            assert_eq!(actual_token.length as usize, source.len(),
                "Incorrect token length for keyword: {}", source);
        }

        // Test that regular identifiers are not treated as keywords
        let mut lexer = create_test_pp_lexer("my_variable");
        let token = lexer.next_token();
        
        assert!(token.is_some(), "Failed to lex identifier");
        match token.unwrap().kind {
            PPTokenKind::Identifier(symbol) => {
                assert_eq!(symbol.as_str(), "my_variable");
            }
            _ => panic!("Expected identifier token"),
        }
    }

    /// Test 4: Check if PPLexer can produce literal tokens
    #[test]
    fn test_literal_tokens() {
        // Test number literals
        let number_literals = vec![
            "42", "0", "123456", "0x1A", "077", "3.14", "1e4"
        ];

        for source in number_literals {
            let mut lexer = create_test_pp_lexer(source);
            let token = lexer.next_token();
            
            assert!(token.is_some(), "Failed to lex number literal: {}", source);
            match token.unwrap().kind {
                PPTokenKind::Number(_) => {},
                _ => panic!("Expected number token for: {}", source),
            }
        }

        // Test string literals
        let string_literals = vec![
            "\"hello\"", "\"world\"", "\"\"", "\"escaped\\nstring\""
        ];

        for source in string_literals {
            let mut lexer = create_test_pp_lexer(source);
            let token = lexer.next_token();
            
            assert!(token.is_some(), "Failed to lex string literal: {}", source);
            match token.unwrap().kind {
                PPTokenKind::StringLiteral(_) => {},
                _ => panic!("Expected string literal for: {}", source),
            }
        }

        // Test character literals
        let char_literals = vec!["'a'", "'\\n'", "'Z'"];

        for source in char_literals {
            let mut lexer = create_test_pp_lexer(source);
            let token = lexer.next_token();
            
            assert!(token.is_some(), "Failed to lex character literal: {}", source);
            match token.unwrap().kind {
                PPTokenKind::CharLiteral(_) => {},
                _ => panic!("Expected character literal for: {}", source),
            }
        }
    }
}
