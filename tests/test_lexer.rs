//! Tests for lexer functionality
//!
//! This module tests the lexer's ability to correctly tokenize C source code
//! and preprocessor directives.

use cendol::file::{FileId, FileManager};
use cendol::preprocessor::lexer::Lexer;
use cendol::preprocessor::token::{DirectiveKind, SourceLocation, TokenKind};

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Creates a new file manager instance
fn create_file_manager() -> FileManager {
    FileManager::new()
}

/// Creates a source location for testing
fn create_test_location(file_id: u32, line: u32) -> SourceLocation {
    SourceLocation::new(FileId(file_id), line, 1)
}

/// Helper function to collect all tokens from a lexer
fn collect_tokens_from_lexer(input: &str, filename: &str) -> Vec<TokenKind> {
    let mut file_manager = create_file_manager();
    let file_id = file_manager.open(filename).unwrap();
    let mut lexer = Lexer::new(input, file_id, false);
    let mut tokens = Vec::new();

    loop {
        let token = lexer.next_token().unwrap();
        if let TokenKind::Eof = token.kind {
            break;
        }
        tokens.push(token.kind);
    }

    tokens
}

/// Helper function to extract token kinds from tokens
fn get_token_kinds(tokens: &[TokenKind]) -> Vec<TokenKind> {
    tokens.to_vec()
}

/// Asserts that two token kind vectors are equal
fn assert_tokens_equal(actual: &[TokenKind], expected: &[TokenKind]) {
    assert_eq!(actual, expected);
}

#[cfg(test)]
mod tests {
    use super::{DirectiveKind, TokenKind, assert_tokens_equal, collect_tokens_from_lexer};

    /// Test basic lexer functionality with preprocessor directives
    #[test]
    fn test_lexer() {
        let input = r#"
#define FIVE 5
FIVE
"#;
        let token_kinds = collect_tokens_from_lexer(input, super::config::TEST_FILENAME);

        let expected_tokens = vec![
            TokenKind::Newline,
            TokenKind::Directive(DirectiveKind::Define),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Identifier("FIVE".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Number("5".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("FIVE".to_string()),
            TokenKind::Newline,
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }

    /// Test lexer with various token types
    #[test]
    fn test_all_tokens() {
        let input = "(){}[];:,.##...\\..++--+-<>";
        let token_kinds = collect_tokens_from_lexer(input, super::config::TEST_FILENAME);

        let expected_tokens = vec![
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::LeftBracket,
            TokenKind::RightBracket,
            TokenKind::Semicolon,
            TokenKind::Colon,
            TokenKind::Comma,
            TokenKind::Dot,
            TokenKind::HashHash,
            TokenKind::Ellipsis,
            TokenKind::Backslash,
            TokenKind::Dot,
            TokenKind::PlusPlus,
            TokenKind::MinusMinus,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::LessThan,
            TokenKind::GreaterThan,
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }

    /// Test lexer with increment operator
    #[test]
    fn test_plusplus() {
        let input = "a++";
        let token_kinds = collect_tokens_from_lexer(input, super::config::TEST_FILENAME);

        let expected_tokens = vec![TokenKind::Identifier("a".to_string()), TokenKind::PlusPlus];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }
}
