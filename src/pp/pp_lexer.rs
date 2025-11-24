use crate::source_manager::{SourceId, SourceLoc};
use symbol_table::GlobalSymbol as Symbol;

// Packed token flags for preprocessor tokens
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct PPTokenFlags: u8 {
        const LEADING_SPACE = 1 << 0;  // Token has leading whitespace
        const STARTS_PP_LINE = 1 << 1; // Token starts a preprocessing line
        const NEEDS_CLEANUP = 1 << 2;  // Token needs cleanup after expansion
    }
}

/// Token kinds for preprocessor tokens
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PPTokenKind {
    // Keywords
    If,
    Ifdef,
    Ifndef,
    Elif,
    Else,
    Endif,
    Define,
    Undef,
    Include,
    Line,
    Pragma,
    Error,
    Warning,
    // Punctuation and operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent, // + - * / %
    And,
    Or,
    Xor,
    Not,
    Tilde, // & | ^ ! ~
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual, // < > <= >= == !=
    LeftShift,
    RightShift, // << >>
    Assign,
    PlusAssign,
    MinusAssign, // = += -=
    StarAssign,
    DivAssign,
    ModAssign, // *= /= %=
    AndAssign,
    OrAssign,
    XorAssign, // &= |= ^=
    LeftShiftAssign,
    RightShiftAssign, // <<= >>=
    Increment,
    Decrement, // ++ --
    Arrow,
    Dot, // -> .
    Question,
    Colon, // ? :
    Comma,
    Semicolon, // , ;
    LeftParen,
    RightParen, // ( )
    LeftBracket,
    RightBracket, // [ ]
    LeftBrace,
    RightBrace, // { }
    Ellipsis,   // ...
    LogicAnd,
    LogicOr, // && ||
    Hash,
    HashHash, // # ##
    // Literals and identifiers
    Identifier(Symbol),    // Interned identifier
    StringLiteral(Symbol), // Interned string literal
    CharLiteral(u32),      // Unicode codepoint value
    Number(Symbol),        // Raw numeric literal text for parser
    // Special
    Eof,
    Unknown,
}

/// Token structure for preprocessor tokens
#[derive(Clone, Copy, Debug)]
pub struct PPToken {
    pub kind: PPTokenKind,
    pub flags: PPTokenFlags,
    pub location: SourceLoc, // Contains file ID and byte offset
    pub length: u16,         // Maximum token length (64KB should be sufficient for any token)
}

impl PPToken {
    /// Create a PPToken with full control over all fields
    pub fn new(kind: PPTokenKind, flags: PPTokenFlags, location: SourceLoc, length: u16) -> Self {
        PPToken {
            kind,
            flags,
            location,
            length,
        }
    }

    /// Create a simple PPToken with empty flags and length 1 (most common case)
    pub fn simple(kind: PPTokenKind, location: SourceLoc) -> Self {
        PPToken::new(kind, PPTokenFlags::empty(), location, 1)
    }

    /// Create a PPToken with text-based length (empty flags)
    pub fn text(kind: PPTokenKind, location: SourceLoc, text: &str) -> Self {
        PPToken::new(kind, PPTokenFlags::empty(), location, text.len() as u16)
    }

    /// Create a PPToken with custom flags and length 1
    pub fn with_flags(kind: PPTokenKind, flags: PPTokenFlags, location: SourceLoc) -> Self {
        PPToken::new(kind, flags, location, 1)
    }

    /// Get the text representation of the token
    pub fn get_text(&self) -> String {
        match &self.kind {
            PPTokenKind::Identifier(sym) => sym.as_str().to_string(),
            PPTokenKind::Number(sym) => sym.as_str().to_string(),
            PPTokenKind::StringLiteral(sym) => sym.as_str().to_string(),
            PPTokenKind::CharLiteral(_) => "'?'".to_string(), // placeholder
            PPTokenKind::LeftParen => "(".to_string(),
            PPTokenKind::RightParen => ")".to_string(),
            PPTokenKind::LeftBracket => "[".to_string(),
            PPTokenKind::RightBracket => "]".to_string(),
            PPTokenKind::LeftBrace => "{".to_string(),
            PPTokenKind::RightBrace => "}".to_string(),
            PPTokenKind::Plus => "+".to_string(),
            PPTokenKind::Minus => "-".to_string(),
            PPTokenKind::Star => "*".to_string(),
            PPTokenKind::Slash => "/".to_string(),
            PPTokenKind::Percent => "%".to_string(),
            PPTokenKind::And => "&".to_string(),
            PPTokenKind::Or => "|".to_string(),
            PPTokenKind::Xor => "^".to_string(),
            PPTokenKind::Not => "!".to_string(),
            PPTokenKind::Tilde => "~".to_string(),
            PPTokenKind::Less => "<".to_string(),
            PPTokenKind::Greater => ">".to_string(),
            PPTokenKind::LessEqual => "<=".to_string(),
            PPTokenKind::GreaterEqual => ">=".to_string(),
            PPTokenKind::Equal => "==".to_string(),
            PPTokenKind::NotEqual => "!=".to_string(),
            PPTokenKind::LeftShift => "<<".to_string(),
            PPTokenKind::RightShift => ">>".to_string(),
            PPTokenKind::Assign => "=".to_string(),
            PPTokenKind::PlusAssign => "+=".to_string(),
            PPTokenKind::MinusAssign => "-=".to_string(),
            PPTokenKind::StarAssign => "*=".to_string(),
            PPTokenKind::DivAssign => "/=".to_string(),
            PPTokenKind::ModAssign => "%=".to_string(),
            PPTokenKind::AndAssign => "&=".to_string(),
            PPTokenKind::OrAssign => "|=".to_string(),
            PPTokenKind::XorAssign => "^=".to_string(),
            PPTokenKind::LeftShiftAssign => "<<=".to_string(),
            PPTokenKind::RightShiftAssign => ">>=".to_string(),
            PPTokenKind::Increment => "++".to_string(),
            PPTokenKind::Decrement => "--".to_string(),
            PPTokenKind::Arrow => "->".to_string(),
            PPTokenKind::Dot => ".".to_string(),
            PPTokenKind::Question => "?".to_string(),
            PPTokenKind::Colon => ":".to_string(),
            PPTokenKind::Comma => ",".to_string(),
            PPTokenKind::Semicolon => ";".to_string(),
            PPTokenKind::Ellipsis => "...".to_string(),
            PPTokenKind::LogicAnd => "&&".to_string(),
            PPTokenKind::LogicOr => "||".to_string(),
            PPTokenKind::Hash => "#".to_string(),
            PPTokenKind::HashHash => "##".to_string(),
            PPTokenKind::If => "if".to_string(),
            PPTokenKind::Ifdef => "ifdef".to_string(),
            PPTokenKind::Ifndef => "ifndef".to_string(),
            PPTokenKind::Elif => "elif".to_string(),
            PPTokenKind::Else => "else".to_string(),
            PPTokenKind::Endif => "endif".to_string(),
            PPTokenKind::Define => "define".to_string(),
            PPTokenKind::Undef => "undef".to_string(),
            PPTokenKind::Include => "include".to_string(),
            PPTokenKind::Line => "line".to_string(),
            PPTokenKind::Pragma => "pragma".to_string(),
            PPTokenKind::Error => "error".to_string(),
            PPTokenKind::Warning => "warning".to_string(),
            PPTokenKind::Eof => "".to_string(),
            PPTokenKind::Unknown => "?".to_string(),
        }
    }
}

/// Manages lexing from different source buffers
pub struct PPLexer {
    pub source_id: SourceId,
    buffer: Vec<u8>,
    pub position: u32, // its okay to use u32 here since source files are limited to 4 MB
    line_starts: Vec<u32>,
    put_back_token: Option<PPToken>,
    pub line_offset: u32,
    pub filename_override: Option<String>,
}

impl PPLexer {
    pub fn new(source_id: SourceId, buffer: Vec<u8>) -> Self {
        let line_starts = vec![0]; // First line starts at offset 0

        PPLexer {
            source_id,
            buffer,
            position: 0,
            line_starts,
            put_back_token: None,
            line_offset: 0,
            filename_override: None,
        }
    }

    /// Get the next character, handling line splicing transparently
    /// Line splicing: backslash followed by newline removes both characters
    pub fn next_char(&mut self) -> Option<u8> {
        if self.position as usize >= self.buffer.len() {
            return None;
        }

        let mut result = self.buffer[self.position as usize];
        self.position += 1;

        // Handle line splicing: backslash followed by newline
        if result == b'\\'
            && (self.position as usize) < self.buffer.len()
            && self.buffer[self.position as usize] == b'\n'
        {
            // Skip the newline too
            self.position += 1;
            // Update line starts - remove the newline from line tracking
            if self.line_starts.len() > 1 {
                self.line_starts.pop();
            }
            // Get the character after the newline for splicing
            if (self.position as usize) < self.buffer.len() {
                result = self.buffer[self.position as usize];
                self.position += 1;
            } else {
                return None;
            }
        }

        Some(result)
    }

    /// Peek at the next character without consuming it, handling line splicing
    pub fn peek_char(&mut self) -> Option<u8> {
        let saved_position = self.position;
        let saved_line_starts = self.line_starts.clone();

        let result = self.next_char();

        // Restore state
        self.position = saved_position;
        self.line_starts = saved_line_starts;

        result
    }

    pub fn next_token(&mut self) -> Option<PPToken> {
        if let Some(token) = self.put_back_token.take() {
            return Some(token);
        }

        self.skip_whitespace_and_comments();

        if self.position as usize >= self.buffer.len() {
            return None;
        }

        let start_pos = self.position;
        let ch = self.next_char().unwrap_or(b' ');

        match ch {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => Some(self.lex_identifier(start_pos, ch)),
            b'0'..=b'9' => Some(self.lex_number(start_pos, ch)),
            b'"' => Some(self.lex_string_literal(start_pos, ch)),
            b'\'' => Some(self.lex_char_literal(start_pos, ch)),
            b'#' => {
                let is_start_of_line = start_pos == *self.line_starts.last().unwrap_or(&0);
                let mut flags = PPTokenFlags::empty();
                if is_start_of_line {
                    flags |= PPTokenFlags::STARTS_PP_LINE;
                }
                let next_ch = self.peek_char();
                if next_ch == Some(b'#') {
                    self.next_char(); // consume the second #
                    Some(PPToken::new(
                        PPTokenKind::HashHash,
                        flags,
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::with_flags(
                        PPTokenKind::Hash,
                        flags,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'+' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'+') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::Increment,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::PlusAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Plus,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'-' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'-') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::Decrement,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::MinusAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else if next_ch == Some(b'>') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::Arrow,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Minus,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'*' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::StarAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Star,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'/' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::DivAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Slash,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'%' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::ModAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Percent,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'=' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::Equal,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Assign,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'!' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::NotEqual,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Not,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'<' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'<') {
                    self.next_char();
                    let next_next_ch = self.peek_char();
                    if next_next_ch == Some(b'=') {
                        self.next_char();
                        Some(PPToken::new(
                            PPTokenKind::LeftShiftAssign,
                            PPTokenFlags::empty(),
                            SourceLoc::new(self.source_id, start_pos),
                            3,
                        ))
                    } else {
                        Some(PPToken::new(
                            PPTokenKind::LeftShift,
                            PPTokenFlags::empty(),
                            SourceLoc::new(self.source_id, start_pos),
                            2,
                        ))
                    }
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::LessEqual,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Less,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'>' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'>') {
                    self.next_char();
                    let next_next_ch = self.peek_char();
                    if next_next_ch == Some(b'=') {
                        self.next_char();
                        Some(PPToken::new(
                            PPTokenKind::RightShiftAssign,
                            PPTokenFlags::empty(),
                            SourceLoc::new(self.source_id, start_pos),
                            3,
                        ))
                    } else {
                        Some(PPToken::new(
                            PPTokenKind::RightShift,
                            PPTokenFlags::empty(),
                            SourceLoc::new(self.source_id, start_pos),
                            2,
                        ))
                    }
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::GreaterEqual,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Greater,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'&' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'&') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::LogicAnd,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::AndAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::And,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'|' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'|') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::LogicOr,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::OrAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Or,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'^' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken::new(
                        PPTokenKind::XorAssign,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        2,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Xor,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'~' => Some(PPToken::simple(
                PPTokenKind::Tilde,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b'.' => {
                let next_ch = self.peek_char();
                let next_next_ch = self.peek_char();
                if next_ch == Some(b'.') && next_next_ch == Some(b'.') {
                    self.next_char(); // consume first '.'
                    self.next_char(); // consume second '.'
                    Some(PPToken::new(
                        PPTokenKind::Ellipsis,
                        PPTokenFlags::empty(),
                        SourceLoc::new(self.source_id, start_pos),
                        3,
                    ))
                } else {
                    Some(PPToken::simple(
                        PPTokenKind::Dot,
                        SourceLoc::new(self.source_id, start_pos),
                    ))
                }
            }
            b'?' => Some(PPToken::simple(
                PPTokenKind::Question,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b':' => Some(PPToken::simple(
                PPTokenKind::Colon,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b',' => Some(PPToken::simple(
                PPTokenKind::Comma,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b';' => Some(PPToken::simple(
                PPTokenKind::Semicolon,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b'(' => Some(PPToken::simple(
                PPTokenKind::LeftParen,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b')' => Some(PPToken::simple(
                PPTokenKind::RightParen,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b'[' => Some(PPToken::simple(
                PPTokenKind::LeftBracket,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b']' => Some(PPToken::simple(
                PPTokenKind::RightBracket,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b'{' => Some(PPToken::simple(
                PPTokenKind::LeftBrace,
                SourceLoc::new(self.source_id, start_pos),
            )),
            b'}' => Some(PPToken::simple(
                PPTokenKind::RightBrace,
                SourceLoc::new(self.source_id, start_pos),
            )),
            _ => Some(PPToken::simple(
                PPTokenKind::Unknown,
                SourceLoc::new(self.source_id, start_pos),
            )),
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace, tracking lines
            while (self.position as usize) < self.buffer.len() {
                let ch = self.buffer[self.position as usize];
                if ch == b'\n' {
                    self.line_starts.push((self.position + 1) as u32);
                    self.position += 1;
                } else if ch.is_ascii_whitespace() {
                    self.position += 1;
                } else {
                    break;
                }
            }

            if self.position as usize >= self.buffer.len() {
                break;
            }

            let ch = self.buffer[self.position as usize];
            if ch == b'/' && self.position as usize + 1 < self.buffer.len() {
                let next_ch = self.buffer[self.position as usize + 1];
                if next_ch == b'/' {
                    // Line comment: skip to end of line
                    self.position += 2;
                    while (self.position as usize) < self.buffer.len()
                        && self.buffer[self.position as usize] != b'\n'
                    {
                        self.position += 1;
                    }
                    // Continue the loop to skip more whitespace/comments
                } else if next_ch == b'*' {
                    // Block comment: skip to */
                    self.position += 2;
                    while self.position as usize + 1 < self.buffer.len() {
                        if self.buffer[self.position as usize] == b'*'
                            && self.buffer[self.position as usize + 1] == b'/'
                        {
                            self.position += 2;
                            break;
                        }
                        if self.buffer[self.position as usize] == b'\n' {
                            self.line_starts.push((self.position + 1) as u32);
                        }
                        self.position += 1;
                    }
                    // Continue the loop to skip more whitespace/comments
                } else {
                    break; // Not a comment, exit loop
                }
            } else {
                break; // Not whitespace or comment start, exit loop
            }
        }
    }

    fn lex_identifier(&mut self, start_pos: u32, first_ch: u8) -> PPToken {
        // Use next_char() for consistency with line splicing
        let mut chars = vec![first_ch];
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                chars.push(self.next_char().unwrap());
            } else {
                break;
            }
        }

        let text = String::from_utf8(chars).unwrap();
        let symbol = Symbol::new(&text);

        // Check for preprocessor keywords
        let kind = match text.as_str() {
            "if" => PPTokenKind::If,
            "ifdef" => PPTokenKind::Ifdef,
            "ifndef" => PPTokenKind::Ifndef,
            "elif" => PPTokenKind::Elif,
            "else" => PPTokenKind::Else,
            "endif" => PPTokenKind::Endif,
            "define" => PPTokenKind::Define,
            "undef" => PPTokenKind::Undef,
            "include" => PPTokenKind::Include,
            "line" => PPTokenKind::Line,
            "pragma" => PPTokenKind::Pragma,
            "error" => PPTokenKind::Error,
            "warning" => PPTokenKind::Warning,
            _ => PPTokenKind::Identifier(symbol),
        };

        PPToken::text(kind, SourceLoc::new(self.source_id, start_pos), &text)
    }

    fn lex_number(&mut self, start_pos: u32, first_ch: u8) -> PPToken {
        // Use next_char() for consistency with line splicing
        let mut chars = vec![first_ch];
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() || ch == b'.' || ch.is_ascii_alphabetic() || ch == b'_' {
                chars.push(self.next_char().unwrap());
            } else {
                break;
            }
        }

        let text = String::from_utf8(chars).unwrap();
        let symbol = Symbol::new(&text);

        PPToken::text(
            PPTokenKind::Number(symbol),
            SourceLoc::new(self.source_id, start_pos),
            &text,
        )
    }

    fn lex_string_literal(&mut self, start_pos: u32, first_ch: u8) -> PPToken {
        // Use next_char() for consistency with line splicing
        let mut chars = vec![first_ch]; // opening quote

        while let Some(ch) = self.next_char() {
            chars.push(ch);
            if ch == b'"' {
                break; // End of string literal
            } else if ch == b'\\' {
                // Handle escape sequences, including line splicing
                if let Some(next_ch) = self.next_char() {
                    chars.push(next_ch);
                    if next_ch == b'\n' {
                        // This is line splicing within a string - the newline is consumed as part of the escape
                        continue;
                    }
                }
            }
        }

        let text = String::from_utf8(chars).unwrap();
        let symbol = Symbol::new(&text);

        PPToken::text(
            PPTokenKind::StringLiteral(symbol),
            SourceLoc::new(self.source_id, start_pos),
            &text,
        )
    }

    fn lex_char_literal(&mut self, start_pos: u32, first_ch: u8) -> PPToken {
        // Use next_char() for consistency with line splicing
        let mut chars = vec![first_ch]; // opening quote
        while let Some(ch) = self.next_char() {
            chars.push(ch);
            if ch == b'\'' {
                break; // End of char literal
            } else if ch == b'\\' {
                // Handle escape sequences
                if let Some(escaped) = self.next_char() {
                    chars.push(escaped);
                }
            }
        }

        // Simplified: just return a placeholder value
        PPToken::new(
            PPTokenKind::CharLiteral(0),
            PPTokenFlags::empty(),
            SourceLoc::new(self.source_id, start_pos),
            chars.len() as u16,
        )
    }

    pub fn put_back(&mut self, token: PPToken) {
        self.put_back_token = Some(token);
    }

    pub fn get_line(&self, offset: u32) -> u32 {
        self.line_starts.partition_point(|&x| x <= offset) as u32 - 1
    }

    pub fn get_current_line(&self) -> u32 {
        self.line_starts.len() as u32 - 1 + self.line_offset
    }
}
