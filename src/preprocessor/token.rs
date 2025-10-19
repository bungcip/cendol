use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
}

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

impl KeywordKind {
    pub fn from_str(s: &str) -> Option<KeywordKind> {
        match s {
            "auto" => Some(KeywordKind::Auto),
            "break" => Some(KeywordKind::Break),
            "case" => Some(KeywordKind::Case),
            "char" => Some(KeywordKind::Char),
            "const" => Some(KeywordKind::Const),
            "continue" => Some(KeywordKind::Continue),
            "default" => Some(KeywordKind::Default),
            "do" => Some(KeywordKind::Do),
            "double" => Some(KeywordKind::Double),
            "else" => Some(KeywordKind::Else),
            "enum" => Some(KeywordKind::Enum),
            "extern" => Some(KeywordKind::Extern),
            "float" => Some(KeywordKind::Float),
            "for" => Some(KeywordKind::For),
            "goto" => Some(KeywordKind::Goto),
            "if" => Some(KeywordKind::If),
            "int" => Some(KeywordKind::Int),
            "long" => Some(KeywordKind::Long),
            "register" => Some(KeywordKind::Register),
            "return" => Some(KeywordKind::Return),
            "short" => Some(KeywordKind::Short),
            "signed" => Some(KeywordKind::Signed),
            "sizeof" => Some(KeywordKind::Sizeof),
            "static" => Some(KeywordKind::Static),
            "struct" => Some(KeywordKind::Struct),
            "switch" => Some(KeywordKind::Switch),
            "typedef" => Some(KeywordKind::Typedef),
            "union" => Some(KeywordKind::Union),
            "unsigned" => Some(KeywordKind::Unsigned),
            "void" => Some(KeywordKind::Void),
            "volatile" => Some(KeywordKind::Volatile),
            "while" => Some(KeywordKind::While),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum PunctKind {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Semicolon,
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

impl fmt::Display for KeywordKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            KeywordKind::Auto => write!(f, "auto"),
            KeywordKind::Break => write!(f, "break"),
            KeywordKind::Case => write!(f, "case"),
            KeywordKind::Char => write!(f, "char"),
            KeywordKind::Const => write!(f, "const"),
            KeywordKind::Continue => write!(f, "continue"),
            KeywordKind::Default => write!(f, "default"),
            KeywordKind::Do => write!(f, "do"),
            KeywordKind::Double => write!(f, "double"),
            KeywordKind::Else => write!(f, "else"),
            KeywordKind::Enum => write!(f, "enum"),
            KeywordKind::Extern => write!(f, "extern"),
            KeywordKind::Float => write!(f, "float"),
            KeywordKind::For => write!(f, "for"),
            KeywordKind::Goto => write!(f, "goto"),
            KeywordKind::If => write!(f, "if"),
            KeywordKind::Int => write!(f, "int"),
            KeywordKind::Long => write!(f, "long"),
            KeywordKind::Register => write!(f, "register"),
            KeywordKind::Return => write!(f, "return"),
            KeywordKind::Short => write!(f, "short"),
            KeywordKind::Signed => write!(f, "signed"),
            KeywordKind::Sizeof => write!(f, "sizeof"),
            KeywordKind::Static => write!(f, "static"),
            KeywordKind::Struct => write!(f, "struct"),
            KeywordKind::Switch => write!(f, "switch"),
            KeywordKind::Typedef => write!(f, "typedef"),
            KeywordKind::Union => write!(f, "union"),
            KeywordKind::Unsigned => write!(f, "unsigned"),
            KeywordKind::Void => write!(f, "void"),
            KeywordKind::Volatile => write!(f, "volatile"),
            KeywordKind::While => write!(f, "while"),
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
            PunctKind::Semicolon => write!(f, ";"),
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
