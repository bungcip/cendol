use crate::preprocessor::token::SourceLocation;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub hideset: HashSet<String>,
    pub location: SourceLocation,
}

impl Token {
    pub fn new(kind: TokenKind, location: SourceLocation) -> Self {
        Token {
            kind,
            hideset: HashSet::new(),
            location,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    Identifier(String),
    Keyword(KeywordKind),
    Number(String),
    String(String),
    Char(String),
    Punct(PunctKind),
    Eof,
}

#[derive(Debug, PartialEq, Clone)]
pub enum KeywordKind {
    Auto,
    Break,
    Case,
    Char,
    Const,
    Continue,
    Default,
    Do,
    Double,
    Else,
    Enum,
    Extern,
    Float,
    For,
    Goto,
    If,
    Int,
    Long,
    Register,
    Return,
    Short,
    Signed,
    Sizeof,
    Static,
    Struct,
    Switch,
    Typedef,
    Union,
    Unsigned,
    Void,
    Volatile,
    While,
}

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

impl From<preprocessor::token::KeywordKind> for KeywordKind {
    fn from(kind: preprocessor::token::KeywordKind) -> Self {
        match kind {
            preprocessor::token::KeywordKind::Auto => KeywordKind::Auto,
            preprocessor::token::KeywordKind::Break => KeywordKind::Break,
            preprocessor::token::KeywordKind::Case => KeywordKind::Case,
            preprocessor::token::KeywordKind::Char => KeywordKind::Char,
            preprocessor::token::KeywordKind::Const => KeywordKind::Const,
            preprocessor::token::KeywordKind::Continue => KeywordKind::Continue,
            preprocessor::token::KeywordKind::Default => KeywordKind::Default,
            preprocessor::token::KeywordKind::Do => KeywordKind::Do,
            preprocessor::token::KeywordKind::Double => KeywordKind::Double,
            preprocessor::token::KeywordKind::Else => KeywordKind::Else,
            preprocessor::token::KeywordKind::Enum => KeywordKind::Enum,
            preprocessor::token::KeywordKind::Extern => KeywordKind::Extern,
            preprocessor::token::KeywordKind::Float => KeywordKind::Float,
            preprocessor::token::KeywordKind::For => KeywordKind::For,
            preprocessor::token::KeywordKind::Goto => KeywordKind::Goto,
            preprocessor::token::KeywordKind::If => KeywordKind::If,
            preprocessor::token::KeywordKind::Int => KeywordKind::Int,
            preprocessor::token::KeywordKind::Long => KeywordKind::Long,
            preprocessor::token::KeywordKind::Register => KeywordKind::Register,
            preprocessor::token::KeywordKind::Return => KeywordKind::Return,
            preprocessor::token::KeywordKind::Short => KeywordKind::Short,
            preprocessor::token::KeywordKind::Signed => KeywordKind::Signed,
            preprocessor::token::KeywordKind::Sizeof => KeywordKind::Sizeof,
            preprocessor::token::KeywordKind::Static => KeywordKind::Static,
            preprocessor::token::KeywordKind::Struct => KeywordKind::Struct,
            preprocessor::token::KeywordKind::Switch => KeywordKind::Switch,
            preprocessor::token::KeywordKind::Typedef => KeywordKind::Typedef,
            preprocessor::token::KeywordKind::Union => KeywordKind::Union,
            preprocessor::token::KeywordKind::Unsigned => KeywordKind::Unsigned,
            preprocessor::token::KeywordKind::Void => KeywordKind::Void,
            preprocessor::token::KeywordKind::Volatile => KeywordKind::Volatile,
            preprocessor::token::KeywordKind::While => KeywordKind::While,
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
                _ => panic!("cannot convert preprocessor punct to parser punct"),
            },
            _ => panic!("cannot convert preprocessor punct to parser punct"),
        }
    }
}
