use std::collections::HashSet;
use std::fmt;

// TODO: Define SourceLocation
type SourceLocation = ();

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub hideset: HashSet<String>,
    pub expansion_locs: Vec<SourceLocation>,
}

impl Token {
    pub fn new(kind: TokenKind) -> Self {
        Token {
            kind,
            hideset: HashSet::new(),
            expansion_locs: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    Identifier(String),
    Keyword(String),
    Number(String),
    String(String),
    Char(String),
    Punct(String),
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
            TokenKind::Keyword(s) => write!(f, "{}", s),
            TokenKind::Number(s) => write!(f, "{}", s),
            TokenKind::String(s) => write!(f, "{}", s),
            TokenKind::Char(s) => write!(f, "{}", s),
            TokenKind::Punct(s) => write!(f, "{}", s),
            TokenKind::Whitespace(s) => write!(f, "{}", s),
            TokenKind::Newline => write!(f, "\n"),
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


impl TokenKind {
    pub fn is_whitespace(&self) -> bool {
        matches!(self, TokenKind::Whitespace(_))
    }
}
