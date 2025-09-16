#[cfg(test)]
mod tests {
    use cendol::preprocessor::lexer::Lexer;
    use cendol::preprocessor::token::{Token, TokenKind};

    #[test]
    fn test_lexer() {
        let input = r#"
#define FIVE 5
FIVE
"#;
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token().unwrap();
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }

        let token_kinds: Vec<TokenKind> = tokens
            .into_iter()
            .map(|t| t.kind)
            .collect();

        let expected_tokens = vec![
            TokenKind::Newline,
            TokenKind::Punct("#".to_string()),
            TokenKind::Identifier("define".to_string()),
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
}