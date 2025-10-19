#[cfg(test)]
mod tests {
    use cendol::file::FileManager;
    use cendol::preprocessor::lexer::Lexer;
    use cendol::preprocessor::token::{DirectiveKind, TokenKind};

    #[test]
    fn test_lexer() {
        let input = r#"
#define FIVE 5
FIVE
"#;
        let mut file_manager = FileManager::new();
        let file_id = file_manager.open("test.c").unwrap();
        let mut lexer = Lexer::new(input, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token().unwrap();
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }

        let token_kinds: Vec<TokenKind> = tokens.into_iter().map(|t| t.kind).collect();

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
        assert_eq!(token_kinds, expected_tokens);
    }

    #[test]
    fn test_all_tokens() {
        let input = "(){}[];:,.##...\\..++--+-<>";
        let mut file_manager = FileManager::new();
        let file_id = file_manager.open("test.c").unwrap();
        let mut lexer = Lexer::new(input, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token().unwrap();
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }

        let token_kinds: Vec<TokenKind> = tokens.into_iter().map(|t| t.kind).collect();

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
        assert_eq!(token_kinds, expected_tokens);
    }

    #[test]
    fn test_plusplus() {
        let input = "a++";
        let mut file_manager = FileManager::new();
        let file_id = file_manager.open("test.c").unwrap();
        let mut lexer = Lexer::new(input, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token().unwrap();
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }

        let token_kinds: Vec<TokenKind> = tokens.into_iter().map(|t| t.kind).collect();

        let expected_tokens = vec![TokenKind::Identifier("a".to_string()), TokenKind::PlusPlus];
        assert_eq!(token_kinds, expected_tokens);
    }
}
