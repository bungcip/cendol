pub use crate::common::{KeywordKind, SourceLocation};
use std::collections::HashSet;

/// Represents a token in the C language.
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// A set of macro names that are hidden from this token.
    pub hideset: HashSet<String>,
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
        Token {
            kind,
            hideset: HashSet::new(),
            location,
        }
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
            preprocessor::token::TokenKind::Keyword(k) => TokenKind::Keyword(k.into()),
            preprocessor::token::TokenKind::Number(s) => TokenKind::Number(s),
            preprocessor::token::TokenKind::String(s) => TokenKind::String(s),
            preprocessor::token::TokenKind::Char(s) => TokenKind::Char(s),
            preprocessor::token::TokenKind::Punct(p) => TokenKind::Punct(p.into()),
            preprocessor::token::TokenKind::Eof => TokenKind::Eof,
            _ => panic!("cannot convert preprocessor token to parser token"),
        };

        Token {
            kind,
            hideset: token.hideset,
            location: token.location,
        }
    }
}

impl From<preprocessor::token::PunctKind> for PunctKind {
    fn from(kind: preprocessor::token::PunctKind) -> Self {
        match kind {
            preprocessor::token::PunctKind::LeftParen => PunctKind::LeftParen,
            preprocessor::token::PunctKind::RightParen => PunctKind::RightParen,
            preprocessor::token::PunctKind::LeftBrace => PunctKind::LeftBrace,
            preprocessor::token::PunctKind::RightBrace => PunctKind::RightBrace,
            preprocessor::token::PunctKind::LeftBracket => PunctKind::LeftBracket,
            preprocessor::token::PunctKind::RightBracket => PunctKind::RightBracket,
            preprocessor::token::PunctKind::Semicolon => PunctKind::Semicolon,
            preprocessor::token::PunctKind::Colon => PunctKind::Colon,
            preprocessor::token::PunctKind::Comma => PunctKind::Comma,
            preprocessor::token::PunctKind::Ellipsis => PunctKind::Ellipsis,
            preprocessor::token::PunctKind::Dot => PunctKind::Dot,
            preprocessor::token::PunctKind::Other(s) => match s.as_str() {
                "+" => PunctKind::Plus,
                "-" => PunctKind::Minus,
                "*" => PunctKind::Star,
                "/" => PunctKind::Slash,
                "=" => PunctKind::Equal,
                "&" => PunctKind::Ampersand,
                "==" => PunctKind::EqualEqual,
                "!=" => PunctKind::BangEqual,
                "<" => PunctKind::LessThan,
                ">" => PunctKind::GreaterThan,
                "<=" => PunctKind::LessThanEqual,
                ">=" => PunctKind::GreaterThanEqual,
                "&&" => PunctKind::AmpersandAmpersand,
                "||" => PunctKind::PipePipe,
                "!" => PunctKind::Bang,
                "++" => PunctKind::PlusPlus,
                "--" => PunctKind::MinusMinus,
                _ => panic!("cannot convert preprocessor punct to parser punct"),
            },
            _ => panic!("cannot convert preprocessor punct to parser punct"),
        }
    }
}
