use crate::file::FileId;
use std::fmt;
use std::str::FromStr;

/// Represents a location in a source file.
#[derive(Debug, PartialEq, Clone, Copy, Default, serde::Serialize)]
pub struct SourceLocation {
    /// The file name.
    pub file: FileId,
    /// The line number.
    pub line: u32,
    /// The column number (1-based).
    pub column: u32,
}

impl SourceLocation {
    /// Creates a new `SourceLocation` instance.
    ///
    /// # Arguments
    ///
    /// * `file` - The file identifier.
    /// * `line` - The line number (1-based).
    /// * `column` - The column number (1-based).
    ///
    /// # Returns
    ///
    /// A new `SourceLocation` instance.
    pub fn new(file: FileId, line: u32, column: u32) -> Self {
        SourceLocation { file, line, column }
    }
}

/// Represents a span in a source file, from start to end.
#[derive(Debug, PartialEq, Clone, Default, Copy, serde::Serialize)]
pub struct SourceSpan {
    /// The file name.
    pub file: FileId,
    /// The start location.
    pub start: SourceLocation,
    /// The end location.
    pub end: SourceLocation,
}

impl SourceSpan {
    /// Creates a new `SourceSpan` instance.
    ///
    /// # Arguments
    ///
    /// * `file` - The file identifier.
    /// * `start` - The start location.
    /// * `end` - The end location.
    ///
    /// # Returns
    ///
    /// A new `SourceSpan` instance.
    pub fn new(file: FileId, start: SourceLocation, end: SourceLocation) -> Self {
        SourceSpan { file, start, end }
    }
}

/// Represents C keywords.
#[derive(Debug, PartialEq, Clone, Copy)]
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
    Inline,
    Int,
    Long,
    LongLong,
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
    Bool,
    Restrict,
    Complex,
    Imaginary,
    Alignof,
    StaticAssert,
    _Noreturn,
}

impl FromStr for KeywordKind {
    type Err = ();

    /// Converts a string slice to a `KeywordKind`.
    ///
    /// # Arguments
    ///
    /// * `s` - The string slice to convert.
    ///
    /// # Returns
    ///
    /// A `Result` containing the `KeywordKind` if the string is a valid keyword, or an empty error if not.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "auto" => Ok(KeywordKind::Auto),
            "break" => Ok(KeywordKind::Break),
            "case" => Ok(KeywordKind::Case),
            "char" => Ok(KeywordKind::Char),
            "const" => Ok(KeywordKind::Const),
            "continue" => Ok(KeywordKind::Continue),
            "default" => Ok(KeywordKind::Default),
            "do" => Ok(KeywordKind::Do),
            "double" => Ok(KeywordKind::Double),
            "else" => Ok(KeywordKind::Else),
            "enum" => Ok(KeywordKind::Enum),
            "extern" => Ok(KeywordKind::Extern),
            "float" => Ok(KeywordKind::Float),
            "for" => Ok(KeywordKind::For),
            "goto" => Ok(KeywordKind::Goto),
            "if" => Ok(KeywordKind::If),
            "inline" => Ok(KeywordKind::Inline),
            "int" => Ok(KeywordKind::Int),
            "long" => Ok(KeywordKind::Long),
            "register" => Ok(KeywordKind::Register),
            "return" => Ok(KeywordKind::Return),
            "short" => Ok(KeywordKind::Short),
            "signed" => Ok(KeywordKind::Signed),
            "sizeof" => Ok(KeywordKind::Sizeof),
            "static" => Ok(KeywordKind::Static),
            "struct" => Ok(KeywordKind::Struct),
            "switch" => Ok(KeywordKind::Switch),
            "typedef" => Ok(KeywordKind::Typedef),
            "union" => Ok(KeywordKind::Union),
            "unsigned" => Ok(KeywordKind::Unsigned),
            "void" => Ok(KeywordKind::Void),
            "volatile" => Ok(KeywordKind::Volatile),
            "while" => Ok(KeywordKind::While),
            "_Bool" => Ok(KeywordKind::Bool),
            "_Complex" => Ok(KeywordKind::Complex),
            "_Imaginary" => Ok(KeywordKind::Imaginary),
            "restrict" => Ok(KeywordKind::Restrict),
            "_Alignof" => Ok(KeywordKind::Alignof),
            "_Static_assert" => Ok(KeywordKind::StaticAssert),
            "_Noreturn" => Ok(KeywordKind::_Noreturn),
            _ => Err(()),
        }
    }
}

impl fmt::Display for KeywordKind {
    /// Formats the `KeywordKind` as a string.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter.
    ///
    /// # Returns
    ///
    /// A `fmt::Result`.
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
            KeywordKind::Inline => write!(f, "inline"),
            KeywordKind::Int => write!(f, "int"),
            KeywordKind::Long => write!(f, "long"),
            KeywordKind::LongLong => write!(f, "long long"),
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
            KeywordKind::Bool => write!(f, "_Bool"),
            KeywordKind::Restrict => write!(f, "restrict"),
            KeywordKind::Complex => write!(f, "_Complex"),
            KeywordKind::Imaginary => write!(f, "_Imaginary"),
            KeywordKind::Alignof => write!(f, "_Alignof"),
            KeywordKind::StaticAssert => write!(f, "_Static_assert"),
            KeywordKind::_Noreturn => write!(f, "_Noreturn"),
        }
    }
}
