//! Tests for lexer functionality
//!
//! This module tests the lexer's ability to correctly tokenize C source code
//! and preprocessor directives.

use cendol::file::FileManager;
use cendol::preprocessor::lexer::Lexer;
use cendol::preprocessor::token::{DirectiveKind, KeywordKind, TokenKind};

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Creates a new file manager instance
fn create_file_manager() -> FileManager {
    FileManager::new()
}

/// Helper function to collect all tokens from a lexer
fn collect_tokens(input: &str, filename: &str) -> Vec<TokenKind> {
    let mut file_manager = create_file_manager();
    let file_id = file_manager.open(filename).unwrap();
    let mut lexer = Lexer::new(input, file_id);
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

/// Helper function to collect all tokens from a lexer
fn collect_tokens_without_whitespace(input: &str) -> Vec<TokenKind> {
    let filename = "test.c";
    let mut file_manager = create_file_manager();
    let file_id = file_manager.open(filename).unwrap();
    let mut lexer = Lexer::new(input, file_id);
    let mut tokens = Vec::new();

    loop {
        let token = lexer.next_token().unwrap();
        match token.kind {
            TokenKind::Whitespace(_) | TokenKind::Newline => continue,
            TokenKind::Eof => break,
            _ => tokens.push(token.kind),
        }
    }

    tokens
}

/// Asserts that two token kind vectors are equal
fn assert_tokens_equal(actual: &[TokenKind], expected: &[TokenKind]) {
    assert_eq!(actual, expected);
}

#[cfg(test)]
mod tests {
    use super::{
        DirectiveKind, KeywordKind, TokenKind, assert_tokens_equal, collect_tokens,
        collect_tokens_without_whitespace,
    };

    /// Test basic lexer functionality with preprocessor directives
    #[test]
    fn test_lexer() {
        let input = r#"
#define FIVE 5
FIVE
"#;
        let token_kinds = collect_tokens(input, super::config::TEST_FILENAME);

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

    #[test]
    fn test_single_char_punct_token() {
        let input = "
        [ ] ( ) { } 
        .  &  *  +  -  ~  !  /  %  <  >  ^  |  ?  :  ;  =  ,  #
        ";
        let token_kinds = collect_tokens_without_whitespace(input);

        let expected_tokens = vec![
            TokenKind::LeftBracket,
            TokenKind::RightBracket,
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::Dot,
            TokenKind::Ampersand,
            TokenKind::Star,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Tilde,
            TokenKind::Bang,
            TokenKind::Slash,
            TokenKind::Percent,
            TokenKind::LessThan,
            TokenKind::GreaterThan,
            TokenKind::Caret,
            TokenKind::Pipe,
            TokenKind::Question,
            TokenKind::Colon,
            TokenKind::Semicolon,
            TokenKind::Equal,
            TokenKind::Comma,
            TokenKind::Hash,
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }

    #[test]
    fn test_multi_char_punct_token() {
        let input = "
        ##   ->   ++   --   <<   >>   <=   >=   ==   !=
        &&   ||   *=   /=   %=   +=   -=   <<=  >>= &=  ^=  |=
        ";
        let token_kinds = collect_tokens_without_whitespace(input);

        let expected_tokens = vec![
            TokenKind::HashHash,
            TokenKind::Arrow,
            TokenKind::PlusPlus,
            TokenKind::MinusMinus,
            TokenKind::LessThanLessThan,
            TokenKind::GreaterThanGreaterThan,
            TokenKind::LessThanEqual,
            TokenKind::GreaterThanEqual,
            TokenKind::EqualEqual,
            TokenKind::BangEqual,
            TokenKind::AmpersandAmpersand,
            TokenKind::PipePipe,
            TokenKind::AsteriskEqual,
            TokenKind::SlashEqual,
            TokenKind::PercentEqual,
            TokenKind::PlusEqual,
            TokenKind::MinusEqual,
            TokenKind::LessThanLessThanEqual,
            TokenKind::GreaterThanGreaterThanEqual,
            TokenKind::AmpersandEqual,
            TokenKind::CaretEqual,
            TokenKind::PipeEqual,
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }

    /// Test lexer with greedy tokens like '++' and '--'
    #[test]
    fn test_greddyness() {
        let input = "+++---<<<>>>&&&|||";
        let token_kinds = collect_tokens_without_whitespace(input);

        let expected_tokens = vec![
            TokenKind::PlusPlus,
            TokenKind::Plus,
            TokenKind::MinusMinus,
            TokenKind::Minus,
            TokenKind::LessThanLessThan,
            TokenKind::LessThan,
            TokenKind::GreaterThanGreaterThan,
            TokenKind::GreaterThan,
            TokenKind::AmpersandAmpersand,
            TokenKind::Ampersand,
            TokenKind::PipePipe,
            TokenKind::Pipe,
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }

    /// Test lexer with token which contain keyword tokens
    #[test]
    fn test_keyword_token() {
        let input = "
        auto        break       case        char        const       continue
        default     do          double      else        enum        extern
        float       for         goto        if          inline      int
        long        register    restrict    return      short       signed
        sizeof      static      struct      switch      typedef     union
        unsigned    void        volatile    while       _Bool       _Complex
        _Imaginary
        ";
        let token_kinds = collect_tokens_without_whitespace(input);

        let expected_tokens = vec![
            TokenKind::Keyword(KeywordKind::Auto),
            TokenKind::Keyword(KeywordKind::Break),
            TokenKind::Keyword(KeywordKind::Case),
            TokenKind::Keyword(KeywordKind::Char),
            TokenKind::Keyword(KeywordKind::Const),
            TokenKind::Keyword(KeywordKind::Continue),
            TokenKind::Keyword(KeywordKind::Default),
            TokenKind::Keyword(KeywordKind::Do),
            TokenKind::Keyword(KeywordKind::Double),
            TokenKind::Keyword(KeywordKind::Else),
            TokenKind::Keyword(KeywordKind::Enum),
            TokenKind::Keyword(KeywordKind::Extern),
            TokenKind::Keyword(KeywordKind::Float),
            TokenKind::Keyword(KeywordKind::For),
            TokenKind::Keyword(KeywordKind::Goto),
            TokenKind::Keyword(KeywordKind::If),
            TokenKind::Keyword(KeywordKind::Inline),
            TokenKind::Keyword(KeywordKind::Int),
            TokenKind::Keyword(KeywordKind::Long),
            TokenKind::Keyword(KeywordKind::Register),
            TokenKind::Keyword(KeywordKind::Restrict),
            TokenKind::Keyword(KeywordKind::Return),
            TokenKind::Keyword(KeywordKind::Short),
            TokenKind::Keyword(KeywordKind::Signed),
            TokenKind::Keyword(KeywordKind::Sizeof),
            TokenKind::Keyword(KeywordKind::Static),
            TokenKind::Keyword(KeywordKind::Struct),
            TokenKind::Keyword(KeywordKind::Switch),
            TokenKind::Keyword(KeywordKind::Typedef),
            TokenKind::Keyword(KeywordKind::Union),
            TokenKind::Keyword(KeywordKind::Unsigned),
            TokenKind::Keyword(KeywordKind::Void),
            TokenKind::Keyword(KeywordKind::Volatile),
            TokenKind::Keyword(KeywordKind::While),
            TokenKind::Keyword(KeywordKind::Bool),
            TokenKind::Keyword(KeywordKind::Complex),
            TokenKind::Keyword(KeywordKind::Imaginary),
        ];
        assert_tokens_equal(&token_kinds, &expected_tokens);
    }
}
