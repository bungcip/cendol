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
#[derive(Clone)]
pub struct PPToken {
    pub kind: PPTokenKind,
    pub flags: PPTokenFlags,
    pub location: SourceLoc, // Contains file ID and byte offset
    pub length: u16,         // Maximum token length (64KB should be sufficient for any token)
}

/// Manages lexing from different source buffers
pub struct PPLexer {
    pub source_id: SourceId,
    buffer: Vec<u8>,
    pub position: usize,
    line_starts: Vec<u32>,
    put_back_token: Option<PPToken>,
    pub line_offset: usize,
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
        if self.position >= self.buffer.len() {
            return None;
        }

        let mut result = self.buffer[self.position];
        self.position += 1;

        // Handle line splicing: backslash followed by newline
        if result == b'\\' && self.position < self.buffer.len() && self.buffer[self.position] == b'\n' {
            // Skip the newline too
            self.position += 1;
            // Update line starts - remove the newline from line tracking
            if self.line_starts.len() > 1 {
                self.line_starts.pop();
            }
            // Get the character after the newline for splicing
            if self.position < self.buffer.len() {
                result = self.buffer[self.position];
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

        if self.position >= self.buffer.len() {
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
                let is_start_of_line = start_pos == *self.line_starts.last().unwrap_or(&0) as usize;
                let mut flags = PPTokenFlags::empty();
                if is_start_of_line {
                    flags |= PPTokenFlags::STARTS_PP_LINE;
                }
                let next_ch = self.peek_char();
                if next_ch == Some(b'#') {
                    self.next_char(); // consume the second #
                    Some(PPToken {
                        kind: PPTokenKind::HashHash,
                        flags,
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Hash,
                        flags,
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'+' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'+') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::Increment,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::PlusAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Plus,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'-' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'-') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::Decrement,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::MinusAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if next_ch == Some(b'>') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::Arrow,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Minus,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'*' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::StarAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Star,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'/' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::DivAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Slash,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'%' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::ModAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Percent,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'=' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::Equal,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Assign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'!' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::NotEqual,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Not,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'<' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'<') {
                    self.next_char();
                    let next_next_ch = self.peek_char();
                    if next_next_ch == Some(b'=') {
                        self.next_char();
                        Some(PPToken {
                            kind: PPTokenKind::LeftShiftAssign,
                            flags: PPTokenFlags::empty(),
                            location: SourceLoc::new(self.source_id, start_pos as u32),
                            length: 3,
                        })
                    } else {
                        Some(PPToken {
                            kind: PPTokenKind::LeftShift,
                            flags: PPTokenFlags::empty(),
                            location: SourceLoc::new(self.source_id, start_pos as u32),
                            length: 2,
                        })
                    }
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::LessEqual,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Less,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'>' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'>') {
                    self.next_char();
                    let next_next_ch = self.peek_char();
                    if next_next_ch == Some(b'=') {
                        self.next_char();
                        Some(PPToken {
                            kind: PPTokenKind::RightShiftAssign,
                            flags: PPTokenFlags::empty(),
                            location: SourceLoc::new(self.source_id, start_pos as u32),
                            length: 3,
                        })
                    } else {
                        Some(PPToken {
                            kind: PPTokenKind::RightShift,
                            flags: PPTokenFlags::empty(),
                            location: SourceLoc::new(self.source_id, start_pos as u32),
                            length: 2,
                        })
                    }
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::GreaterEqual,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Greater,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'&' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'&') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::LogicAnd,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::AndAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::And,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'|' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'|') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::LogicOr,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::OrAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Or,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'^' => {
                let next_ch = self.peek_char();
                if next_ch == Some(b'=') {
                    self.next_char();
                    Some(PPToken {
                        kind: PPTokenKind::XorAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Xor,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'~' => {
                Some(PPToken {
                    kind: PPTokenKind::Tilde,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'.' => {
                let next_ch = self.peek_char();
                let next_next_ch = self.peek_char();
                if next_ch == Some(b'.') && next_next_ch == Some(b'.') {
                    self.next_char(); // consume first '.'
                    self.next_char(); // consume second '.'
                    Some(PPToken {
                        kind: PPTokenKind::Ellipsis,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 3,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Dot,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'?' => {
                Some(PPToken {
                    kind: PPTokenKind::Question,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b':' => {
                Some(PPToken {
                    kind: PPTokenKind::Colon,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b',' => {
                Some(PPToken {
                    kind: PPTokenKind::Comma,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b';' => {
                Some(PPToken {
                    kind: PPTokenKind::Semicolon,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'(' => {
                Some(PPToken {
                    kind: PPTokenKind::LeftParen,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b')' => {
                Some(PPToken {
                    kind: PPTokenKind::RightParen,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'[' => {
                Some(PPToken {
                    kind: PPTokenKind::LeftBracket,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b']' => {
                Some(PPToken {
                    kind: PPTokenKind::RightBracket,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'{' => {
                Some(PPToken {
                    kind: PPTokenKind::LeftBrace,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'}' => {
                Some(PPToken {
                    kind: PPTokenKind::RightBrace,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            _ => {
                Some(PPToken {
                    kind: PPTokenKind::Unknown,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
        }
    }

    #[allow(dead_code)]
    fn skip_whitespace(&mut self) {
        while self.position < self.buffer.len() {
            let ch = self.buffer[self.position];
            if ch.is_ascii_whitespace() {
                self.position += 1;
            } else {
                break;
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace, tracking lines
            while self.position < self.buffer.len() {
                let ch = self.buffer[self.position];
                if ch == b'\n' {
                    self.line_starts.push((self.position + 1) as u32);
                    self.position += 1;
                } else if ch.is_ascii_whitespace() {
                    self.position += 1;
                } else {
                    break;
                }
            }

            if self.position >= self.buffer.len() {
                break;
            }

            let ch = self.buffer[self.position];
            if ch == b'/' && self.position + 1 < self.buffer.len() {
                let next_ch = self.buffer[self.position + 1];
                if next_ch == b'/' {
                    // Line comment: skip to end of line
                    self.position += 2;
                    while self.position < self.buffer.len() && self.buffer[self.position] != b'\n' {
                        self.position += 1;
                    }
                    // Continue the loop to skip more whitespace/comments
                } else if next_ch == b'*' {
                    // Block comment: skip to */
                    self.position += 2;
                    while self.position + 1 < self.buffer.len() {
                        if self.buffer[self.position] == b'*'
                            && self.buffer[self.position + 1] == b'/'
                        {
                            self.position += 2;
                            break;
                        }
                        if self.buffer[self.position] == b'\n' {
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

    fn lex_identifier(&mut self, start_pos: usize, first_ch: u8) -> PPToken {
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

        PPToken {
            kind,
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: text.len() as u16,
        }
    }

    fn lex_number(&mut self, start_pos: usize, first_ch: u8) -> PPToken {
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

        PPToken {
            kind: PPTokenKind::Number(symbol),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: text.len() as u16,
        }
    }

    fn lex_string_literal(&mut self, start_pos: usize, first_ch: u8) -> PPToken {
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

        PPToken {
            kind: PPTokenKind::StringLiteral(symbol),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: text.len() as u16,
        }
    }

    fn lex_char_literal(&mut self, start_pos: usize, first_ch: u8) -> PPToken {
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
        PPToken {
            kind: PPTokenKind::CharLiteral(0),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: chars.len() as u16,
        }
    }

    pub fn put_back(&mut self, token: PPToken) {
        self.put_back_token = Some(token);
    }

    pub fn get_line(&self, offset: u32) -> usize {
        self.line_starts.partition_point(|&x| x <= offset) - 1
    }

    pub fn get_current_line(&self) -> usize {
        self.line_starts.len() - 1 + self.line_offset
    }
}

