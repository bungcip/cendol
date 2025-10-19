pub use crate::common::{KeywordKind, SourceLocation};
use std::collections::HashSet;
use std::fmt;

/// Represents a token in the C preprocessor.
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// A set of macro names that are hidden from this token.
    pub hideset: HashSet<String>,
    /// The location of the token in the source code.
    pub location: SourceLocation,
    /// The locations of macro expansions that produced this token.
    pub expansion_locs: Vec<SourceLocation>,
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
            expansion_locs: Vec::new(),
        }
    }
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
    Hash,
    HashHash,
    Ellipsis,
    Backslash,
    Dot,
    Other(String),
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
    /// Whitespace.
    Whitespace(String),
    /// A newline character.
    Newline,
    /// A comment.
    Comment(String),
    /// A preprocessor directive.
    Directive(String),
    /// The `#if` directive.
    If,
    /// The `#else` directive.
    Else,
    /// The `#elif` directive.
    Elif,
    /// The `#endif` directive.
    Endif,
    /// The `#ifdef` directive.
    Ifdef,
    /// The `#ifndef` directive.
    Ifndef,
    /// The `#undef` directive.
    Undef,
    /// The `#error` directive.
    Error,
    /// The `#line` directive.
    Line,
    /// The `#include` directive.
    Include,
    /// The end of the input.
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
    /// Returns `true` if the token is whitespace.
    pub fn is_whitespace(&self) -> bool {
        matches!(self, TokenKind::Whitespace(_))
    }
}
