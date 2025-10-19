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
    /// A punctuation mark.
    Punct(PunctKind),
    /// The end of the input.
    Eof,
}

/// The kind of a punctuation mark.
#[derive(Debug, PartialEq, Clone)]
pub enum PunctKind {
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
    PipePipe,
    Bang,
    Ampersand,
    Ellipsis,
    Dot,
    PlusPlus,
    MinusMinus,
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
            preprocessor::token::TokenKind::LeftParen => TokenKind::Punct(PunctKind::LeftParen),
            preprocessor::token::TokenKind::RightParen => TokenKind::Punct(PunctKind::RightParen),
            preprocessor::token::TokenKind::LeftBrace => TokenKind::Punct(PunctKind::LeftBrace),
            preprocessor::token::TokenKind::RightBrace => TokenKind::Punct(PunctKind::RightBrace),
            preprocessor::token::TokenKind::LeftBracket => TokenKind::Punct(PunctKind::LeftBracket),
            preprocessor::token::TokenKind::RightBracket => {
                TokenKind::Punct(PunctKind::RightBracket)
            }
            preprocessor::token::TokenKind::Semicolon => TokenKind::Punct(PunctKind::Semicolon),
            preprocessor::token::TokenKind::Colon => TokenKind::Punct(PunctKind::Colon),
            preprocessor::token::TokenKind::Comma => TokenKind::Punct(PunctKind::Comma),
            preprocessor::token::TokenKind::Ellipsis => TokenKind::Punct(PunctKind::Ellipsis),
            preprocessor::token::TokenKind::Dot => TokenKind::Punct(PunctKind::Dot),
            preprocessor::token::TokenKind::Plus => TokenKind::Punct(PunctKind::Plus),
            preprocessor::token::TokenKind::Minus => TokenKind::Punct(PunctKind::Minus),
            preprocessor::token::TokenKind::PlusPlus => TokenKind::Punct(PunctKind::PlusPlus),
            preprocessor::token::TokenKind::MinusMinus => TokenKind::Punct(PunctKind::MinusMinus),
            preprocessor::token::TokenKind::Equal => TokenKind::Punct(PunctKind::Equal),
            preprocessor::token::TokenKind::LessThan => TokenKind::Punct(PunctKind::LessThan),
            preprocessor::token::TokenKind::GreaterThan => TokenKind::Punct(PunctKind::GreaterThan),
            preprocessor::token::TokenKind::Eof => TokenKind::Eof,
            _ => panic!("cannot convert preprocessor token to parser token"),
        };

        Token {
            kind,
            location: token.location,
        }
    }
}
