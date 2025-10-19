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
    Plus,
    Minus,
    PlusPlus,
    MinusMinus,
    Star,
    Slash,
    Pipe,
    PipePipe,
    Ampersand,
    AmpersandAmpersand,
    Caret,
    Tilde,
    Bang,
    Question,
    Equal,
    LessThan,
    GreaterThan,
    /// Whitespace.
    Whitespace(String),
    /// A newline character.
    Newline,
    /// A comment.
    Comment(String),
    /// A preprocessor directive.
    Directive(DirectiveKind),
    /// The end of the input.
    Eof,
}

/// The kind of a preprocessor directive.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum DirectiveKind {
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
    /// The `#define` directive.
    Define,
}

/// The kind of an include directive.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum IncludeKind {
    /// An include directive with angle brackets.
    System,
    /// An include directive with double quotes.
    Local,
}


impl fmt::Display for DirectiveKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DirectiveKind::If => write!(f, "#if"),
            DirectiveKind::Else => write!(f, "#else"),
            DirectiveKind::Elif => write!(f, "#elif"),
            DirectiveKind::Endif => write!(f, "#endif"),
            DirectiveKind::Ifdef => write!(f, "#ifdef"),
            DirectiveKind::Ifndef => write!(f, "#ifndef"),
            DirectiveKind::Undef => write!(f, "#undef"),
            DirectiveKind::Error => write!(f, "#error"),
            DirectiveKind::Line => write!(f, "#line"),
            DirectiveKind::Include => write!(f, "#include"),
            DirectiveKind::Define => write!(f, "#define"),
        }
    }
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
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::LeftBrace => write!(f, "{{"),
            TokenKind::RightBrace => write!(f, "}}"),
            TokenKind::LeftBracket => write!(f, "["),
            TokenKind::RightBracket => write!(f, "]"),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Hash => write!(f, "#"),
            TokenKind::HashHash => write!(f, "##"),
            TokenKind::Ellipsis => write!(f, "..."),
            TokenKind::Backslash => write!(f, "\\"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::PlusPlus => write!(f, "++"),
            TokenKind::MinusMinus => write!(f, "--"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::PipePipe => write!(f, "||"),
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::AmpersandAmpersand => write!(f, "&&"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::Tilde => write!(f, "~"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Question => write!(f, "?"),
            TokenKind::Equal => write!(f, "="),
            TokenKind::LessThan => write!(f, "<"),
            TokenKind::GreaterThan => write!(f, ">"),
            TokenKind::Whitespace(s) => write!(f, "{}", s),
            TokenKind::Newline => writeln!(f),
            TokenKind::Comment(s) => write!(f, "{}", s),
            TokenKind::Directive(d) => write!(f, "{}", d),
            TokenKind::Eof => write!(f, ""),
        }
    }
}

impl TokenKind {
    /// Returns `true` if the token is whitespace.
    pub fn is_whitespace(&self) -> bool {
        matches!(self, TokenKind::Whitespace(_))
    }
}
