pub use crate::common::{KeywordKind, SourceLocation};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub hideset: HashSet<String>,
    pub location: SourceLocation,
    pub expansion_locs: Vec<SourceLocation>,
}

impl Token {
    pub fn new(kind: TokenKind, location: SourceLocation) -> Self {
        Token {
            kind,
            hideset: HashSet::new(),
            location,
            expansion_locs: Vec::new(),
        }
    }
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
    Hash,
    HashHash,
    Ellipsis,
    Backslash,
    Dot,
    Other(String),
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    Identifier(String),
    Keyword(KeywordKind),
    Number(String),
    String(String),
    Char(String),
    Punct(PunctKind),
    Whitespace(String),
    Newline,
    Comment(String),
    Directive(String),
    If,
    Else,
    Elif,
    Endif,
    Ifdef,
    Ifndef,
    Undef,
    Error,
    Line,
    Include,
    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::Identifier(s) => write!(f, "{}", s),
            TokenKind::Keyword(k) => write!(f, "{}", k),
            TokenKind::Number(s) => write!(f, "{}", s),
            TokenKind::String(s) => write!(f, "{}", s),
            TokenKind::Char(s) => write!(f, "{}", s),
            TokenKind::Punct(p) => write!(f, "{}", p),
            TokenKind::Whitespace(s) => write!(f, "{}", s),
            TokenKind::Newline => writeln!(f),
            TokenKind::Comment(s) => write!(f, "{}", s),
            TokenKind::Directive(s) => write!(f, "{}", s),
            TokenKind::If => write!(f, "#if"),
            TokenKind::Else => write!(f, "#else"),
            TokenKind::Elif => write!(f, "#elif"),
            TokenKind::Endif => write!(f, "#endif"),
            TokenKind::Ifdef => write!(f, "#ifdef"),
            TokenKind::Ifndef => write!(f, "#ifndef"),
            TokenKind::Undef => write!(f, "#undef"),
            TokenKind::Error => write!(f, "#error"),
            TokenKind::Line => write!(f, "#line"),
            TokenKind::Include => write!(f, "#include"),
            TokenKind::Eof => write!(f, ""),
        }
    }
}

impl fmt::Display for PunctKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PunctKind::LeftParen => write!(f, "("),
            PunctKind::RightParen => write!(f, ")"),
            PunctKind::LeftBrace => write!(f, "{{"),
            PunctKind::RightBrace => write!(f, "}}"),
            PunctKind::LeftBracket => write!(f, "["),
            PunctKind::RightBracket => write!(f, "]"),
            PunctKind::Semicolon => write!(f, ";"),
            PunctKind::Colon => write!(f, ":"),
            PunctKind::Comma => write!(f, ","),
            PunctKind::Hash => write!(f, "#"),
            PunctKind::HashHash => write!(f, "##"),
            PunctKind::Ellipsis => write!(f, "..."),
            PunctKind::Backslash => write!(f, "\\"),
            PunctKind::Dot => write!(f, "."),
            PunctKind::Other(s) => write!(f, "{}", s),
        }
    }
}

impl TokenKind {
    pub fn is_whitespace(&self) -> bool {
        matches!(self, TokenKind::Whitespace(_))
    }
}
