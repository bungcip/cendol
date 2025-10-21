pub use crate::common::{KeywordKind, SourceLocation};

/// Represents a token in the C language.
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// The location of the token in the source code.
    pub location: SourceLocation,
}

impl Token {
    /// Creates a new `Token`.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind of token.
    /// * `location` - The location of the token in the source code.
    ///
    /// # Returns
    ///
    /// A new `Token` instance.
    pub fn new(kind: TokenKind, location: SourceLocation) -> Self {
        Token { kind, location }
    }
}

/// The kind of a token.
#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    /// An identifier.
    Identifier(String),
    /// A keyword.
    Keyword(KeywordKind),
    /// A number literal.
    Number(String),
    /// A string literal.
    String(String),
    /// A character literal.
    Char(String),
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Semicolon,
    Colon,
    Comma,
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    EqualEqual,
    BangEqual,
    LessThan,
    GreaterThan,
    LessThanEqual,
    GreaterThanEqual,
    AmpersandAmpersand,
    Pipe,
    PipePipe,
    Bang,
    Ampersand,
    Caret,
    Tilde,
    Question,
    Ellipsis,
    Dot,
    PlusPlus,
    MinusMinus,
    /// The end of the input.
    Eof,
}
use crate::preprocessor;

impl From<preprocessor::token::Token> for Token {
    fn from(token: preprocessor::token::Token) -> Self {
        let kind = match token.kind {
            preprocessor::token::TokenKind::Identifier(s) => TokenKind::Identifier(s),
            preprocessor::token::TokenKind::Keyword(k) => TokenKind::Keyword(k),
            preprocessor::token::TokenKind::Number(s) => TokenKind::Number(s),
            preprocessor::token::TokenKind::String(s) => TokenKind::String(s),
            preprocessor::token::TokenKind::Char(s) => TokenKind::Char(s),
            preprocessor::token::TokenKind::LeftParen => TokenKind::LeftParen,
            preprocessor::token::TokenKind::RightParen => TokenKind::RightParen,
            preprocessor::token::TokenKind::LeftBrace => TokenKind::LeftBrace,
            preprocessor::token::TokenKind::RightBrace => TokenKind::RightBrace,
            preprocessor::token::TokenKind::LeftBracket => TokenKind::LeftBracket,
            preprocessor::token::TokenKind::RightBracket => TokenKind::RightBracket,
            preprocessor::token::TokenKind::Semicolon => TokenKind::Semicolon,
            preprocessor::token::TokenKind::Colon => TokenKind::Colon,
            preprocessor::token::TokenKind::Comma => TokenKind::Comma,
            preprocessor::token::TokenKind::Ellipsis => TokenKind::Ellipsis,
            preprocessor::token::TokenKind::Dot => TokenKind::Dot,
            preprocessor::token::TokenKind::Plus => TokenKind::Plus,
            preprocessor::token::TokenKind::Minus => TokenKind::Minus,
            preprocessor::token::TokenKind::PlusPlus => TokenKind::PlusPlus,
            preprocessor::token::TokenKind::MinusMinus => TokenKind::MinusMinus,
            preprocessor::token::TokenKind::Star => TokenKind::Star,
            preprocessor::token::TokenKind::Equal => TokenKind::Equal,
            preprocessor::token::TokenKind::LessThan => TokenKind::LessThan,
            preprocessor::token::TokenKind::GreaterThan => TokenKind::GreaterThan,
            preprocessor::token::TokenKind::Pipe => TokenKind::Pipe,
            preprocessor::token::TokenKind::PipePipe => TokenKind::PipePipe,
            preprocessor::token::TokenKind::Ampersand => TokenKind::Ampersand,
            preprocessor::token::TokenKind::AmpersandAmpersand => TokenKind::AmpersandAmpersand,
            preprocessor::token::TokenKind::Caret => TokenKind::Caret,
            preprocessor::token::TokenKind::Tilde => TokenKind::Tilde,
            preprocessor::token::TokenKind::Bang => TokenKind::Bang,
            preprocessor::token::TokenKind::Question => TokenKind::Question,
            preprocessor::token::TokenKind::Eof => TokenKind::Eof,
            _ => panic!("cannot convert preprocessor token to parser token"),
        };

        Token {
            kind,
            location: token.location,
        }
    }
}
