use std::path::PathBuf;
use std::collections::HashMap;
use symbol_table::GlobalSymbol as Symbol;
use crate::source_manager::{SourceManager, SourceId, SourceSpan, SourceLoc};
use target_lexicon::Triple as TargetInfo;
use chrono::{DateTime, Datelike, Timelike, Utc};
use bitflags::bitflags;
use crate::diagnostic::DiagnosticEngine;

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
    If, Ifdef, Ifndef, Elif, Else, Endif, Define, Undef, Include, Line, Pragma,
    // Punctuation and operators
    Plus, Minus, Star, Slash, Percent, // + - * / %
    And, Or, Xor, Not, Tilde, // & | ^ ! ~
    Less, Greater, LessEqual, GreaterEqual, Equal, NotEqual, // < > <= >= == !=
    LeftShift, RightShift, // << >>
    Assign, PlusAssign, MinusAssign, // = += -=
    StarAssign, DivAssign, ModAssign, // *= /= %=
    AndAssign, OrAssign, XorAssign, // &= |= ^=
    LeftShiftAssign, RightShiftAssign, // <<= >>=
    Increment, Decrement, // ++ --
    Arrow, Dot, // -> .
    Question, Colon, // ? :
    Comma, Semicolon, // , ;
    LeftParen, RightParen, // ( )
    LeftBracket, RightBracket, // [ ]
    LeftBrace, RightBrace, // { }
    Ellipsis, // ...
    LogicAnd, LogicOr, // && ||
    Hash, HashHash, // # ##
    // Literals and identifiers
    Identifier(Symbol),    // Interned identifier
    StringLiteral(Symbol), // Interned string literal
    CharLiteral(u32),      // Unicode codepoint value
    Number(i64),           // Parsed numeric value for preprocessor evaluation
    // Special
    Eof, Unknown,
}

/// Token structure for preprocessor tokens
#[derive(Clone)]
pub struct PPToken {
    pub kind: PPTokenKind,
    pub flags: PPTokenFlags,
    pub location: SourceLoc, // Contains file ID and byte offset
    pub length: u16, // Maximum token length (64KB should be sufficient for any token)
}

/// Language options affecting preprocessor behavior
#[derive(Clone)]
pub struct LangOptions {
    pub c11: bool,              // C11 standard compliance
    pub gnu_mode: bool,         // GNU extensions
    pub ms_extensions: bool,    // Microsoft extensions
}

/// Packed boolean flags for macro properties
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct MacroFlags: u8 {
        const FUNCTION_LIKE = 1 << 0;
        const C99_VARARGS = 1 << 1;
        const GNU_VARARGS = 1 << 2;
        const BUILTIN = 1 << 3;
        const DISABLED = 1 << 4;
        const USED = 1 << 5;
    }
}

/// Represents a macro definition
#[derive(Clone)]
pub struct MacroInfo {
    pub location: SourceLoc,
    pub flags: MacroFlags, // Packed boolean flags
    pub tokens: Vec<PPToken>,
    pub parameter_list: Vec<Symbol>,
    pub variadic_arg: Option<Symbol>,
}

/// Represents conditional compilation state
#[derive(Clone)]
pub struct PPConditionalInfo {
    if_loc: SourceLoc,
    was_skipping: bool,
    found_else: bool,
    found_non_skipping: bool,
}

/// Manages header search paths and include resolution
#[derive(Clone)]
pub struct HeaderSearch {
    search_path: Vec<SearchPath>,
    system_path: Vec<SearchPath>,
    framework_path: Vec<SearchPath>,
    quoted_includes: Vec<String>,
    angled_includes: Vec<String>,
}

#[derive(Clone)]
pub struct SearchPath {
    pub path: PathBuf,
    pub is_system: bool,
}

/// File information for tracking source files
#[derive(Clone)]
pub struct FileInfo {
    pub file_id: SourceId,
    pub path: PathBuf,
    pub size: u32,
    pub buffer_index: usize, // Index into buffers Vec
    pub line_starts: Vec<u32>, // Line start offsets for efficient line lookup
}

/// Include stack information
#[derive(Clone)]
pub struct IncludeStackInfo {
    pub file_id: SourceId,
    pub location: SourceLoc,
}

/// Configuration for preprocessor
#[derive(Debug, Clone)]
pub struct PreprocessorConfig {
    pub max_include_depth: usize,
    pub system_include_paths: Vec<PathBuf>,
}

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    source_manager: &'src mut SourceManager,
    diag: &'src DiagnosticEngine,
    lang_opts: LangOptions,
    target_info: TargetInfo,

    // Macro management
    macros: HashMap<Symbol, MacroInfo>,

    // Conditional compilation state
    conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    include_stack: Vec<IncludeStackInfo>,
    header_search: HeaderSearch,

    // Token management
    cur_token_lexer: Option<Box<PPTokenLexer>>,
    cur_lexer: Option<Box<PPLexer>>,

    // State
    in_main_file: bool,
    is_parsing_main_file: bool,
    include_depth: usize,
}

/// Specialized lexer for macro expansion and token manipulation
pub struct PPTokenLexer {
    // Implementation for macro expansion
}

/// Manages lexing from different source buffers
pub struct PPLexer {
    source_id: SourceId,
    buffer: Vec<u8>,
    position: usize,
    line_starts: Vec<u32>,
}

/// Preprocessor errors
#[derive(Debug, thiserror::Error)]
pub enum PreprocessorError {
    #[error("File not found")]
    FileNotFound,
    #[error("Invalid UTF-8 sequence")]
    InvalidUtf8,
    #[error("Include depth exceeded")]
    IncludeDepthExceeded,
    #[error("Macro redefinition")]
    MacroRedefinition,
    #[error("Expected identifier")]
    ExpectedIdentifier,
    #[error("Invalid directive")]
    InvalidDirective,
    #[error("Unexpected end of file")]
    UnexpectedEndOfFile,
    #[error("Invalid macro parameter")]
    InvalidMacroParameter,
    #[error("Invalid include path")]
    InvalidIncludePath,
    #[error("Unmatched #endif")]
    UnmatchedEndif,
}

impl<'src> Preprocessor<'src> {
    /// Create a new preprocessor
    pub fn new(
        source_manager: &'src mut SourceManager,
        diag: &'src DiagnosticEngine,
        lang_opts: LangOptions,
        target_info: TargetInfo,
        config: &PreprocessorConfig,
    ) -> Self {
        let header_search = HeaderSearch {
            search_path: config.system_include_paths.iter().map(|p| SearchPath {
                path: p.clone(),
                is_system: true,
            }).collect(),
            system_path: Vec::new(),
            framework_path: Vec::new(),
            quoted_includes: Vec::new(),
            angled_includes: Vec::new(),
        };

        let mut preprocessor = Preprocessor {
            source_manager,
            diag,
            lang_opts,
            target_info,
            macros: HashMap::new(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            cur_token_lexer: None,
            cur_lexer: None,
            in_main_file: true,
            is_parsing_main_file: true,
            include_depth: 0,
        };

        preprocessor.initialize_builtin_macros();
        preprocessor
    }

    /// Initialize built-in macros
    fn initialize_builtin_macros(&mut self) {
        let now: DateTime<Utc> = Utc::now();

        // __DATE__
        let date_str = format!("\"{:02} {:02} {}\"",
            now.format("%b"),
            now.day(),
            now.year());
        let date_tokens = self.tokenize_string(&date_str);
        self.define_builtin_macro("__DATE__", date_tokens);

        // __TIME__
        let time_str = format!("\"{:02}:{:02}:{:02}\"",
            now.hour(),
            now.minute(),
            now.second());
        let time_tokens = self.tokenize_string(&time_str);
        self.define_builtin_macro("__TIME__", time_tokens);

        // Other built-ins
        self.define_builtin_macro("__STDC__", vec![PPToken {
            kind: PPTokenKind::Number(1),
            flags: PPTokenFlags::empty(),
            location: SourceLoc(0),
            length: 1,
        }]);

        if self.lang_opts.c11 {
            self.define_builtin_macro("__STDC_VERSION__", vec![PPToken {
                kind: PPTokenKind::Number(201112),
                flags: PPTokenFlags::empty(),
                location: SourceLoc(0),
                length: 6,
            }]);
        }
    }

    /// Define a built-in macro
    fn define_builtin_macro(&mut self, name: &str, tokens: Vec<PPToken>) {
        let symbol = Symbol::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc(0),
            flags: MacroFlags::BUILTIN,
            tokens,
            parameter_list: Vec::new(),
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Tokenize a string into PP tokens (simplified)
    fn tokenize_string(&self, s: &str) -> Vec<PPToken> {
        vec![PPToken {
            kind: PPTokenKind::StringLiteral(Symbol::new(s)),
            flags: PPTokenFlags::empty(),
            location: SourceLoc(0),
            length: s.len() as u16,
        }]
    }

    /// Process source file and return preprocessed tokens
    pub fn process(&mut self, source_id: SourceId, _config: &PreprocessorConfig) -> Result<Vec<PPToken>, PreprocessorError> {
        // Initialize lexer for main file
        let content = self.source_manager.get_file_content(source_id)
            .ok_or(PreprocessorError::FileNotFound)?;

        let lexer = PPLexer::new(source_id, content.as_bytes().to_vec());
        self.cur_lexer = Some(Box::new(lexer));

        let mut result_tokens = Vec::new();

        // Process tokens
        while let Some(token) = self.lex_token() {
            match token.kind {
                PPTokenKind::Hash if token.flags.contains(PPTokenFlags::STARTS_PP_LINE) => {
                    // Handle directive
                    self.handle_directive()?;
                }
                PPTokenKind::Identifier(symbol) => {
                    // Check for macro expansion
                    if let Some(expanded) = self.expand_macro(symbol, token.location)? {
                        result_tokens.extend(expanded);
                    } else {
                        result_tokens.push(token);
                    }
                }
                _ => {
                    result_tokens.push(token);
                }
            }
        }

        // Add EOF token
        result_tokens.push(PPToken {
            kind: PPTokenKind::Eof,
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(source_id, content.len() as u32),
            length: 0,
        });

        Ok(result_tokens)
    }

    /// Lex the next token
    fn lex_token(&mut self) -> Option<PPToken> {
        if let Some(ref mut lexer) = self.cur_lexer {
            lexer.next_token()
        } else {
            None
        }
    }

    /// Handle preprocessor directives
    fn handle_directive(&mut self) -> Result<(), PreprocessorError> {
        let token = self.lex_token().ok_or(PreprocessorError::UnexpectedEndOfFile)?;

        match token.kind {
            PPTokenKind::Define => self.handle_define()?,
            PPTokenKind::Undef => self.handle_undef()?,
            PPTokenKind::Include => self.handle_include()?,
            PPTokenKind::If => self.handle_if()?,
            PPTokenKind::Ifdef => self.handle_ifdef()?,
            PPTokenKind::Ifndef => self.handle_ifndef()?,
            PPTokenKind::Elif => self.handle_elif()?,
            PPTokenKind::Else => self.handle_else()?,
            PPTokenKind::Endif => self.handle_endif()?,
            PPTokenKind::Line => self.handle_line()?,
            PPTokenKind::Pragma => self.handle_pragma()?,
            _ => return Err(PreprocessorError::InvalidDirective),
        }

        Ok(())
    }

    /// Placeholder implementations for directive handlers
    fn handle_define(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_undef(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_include(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_if(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_ifdef(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_ifndef(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_elif(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_else(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_endif(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_line(&mut self) -> Result<(), PreprocessorError> { Ok(()) }
    fn handle_pragma(&mut self) -> Result<(), PreprocessorError> { Ok(()) }

    /// Placeholder for macro expansion
    fn expand_macro(&mut self, _symbol: Symbol, _location: SourceLoc) -> Result<Option<Vec<PPToken>>, PreprocessorError> {
        Ok(None)
    }
}

impl PPLexer {
    pub fn new(source_id: SourceId, buffer: Vec<u8>) -> Self {
        let mut line_starts = Vec::new();
        line_starts.push(0); // First line starts at offset 0

        PPLexer {
            source_id,
            buffer,
            position: 0,
            line_starts,
        }
    }

    pub fn next_token(&mut self) -> Option<PPToken> {
        self.skip_whitespace();

        if self.position >= self.buffer.len() {
            return None;
        }

        let start_pos = self.position;
        let ch = self.buffer[self.position];

        match ch {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => Some(self.lex_identifier(start_pos)),
            b'0'..=b'9' => Some(self.lex_number(start_pos)),
            b'"' => Some(self.lex_string_literal(start_pos)),
            b'\'' => Some(self.lex_char_literal(start_pos)),
            b'#' => {
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'#' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::HashHash,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else {
                    Some(PPToken {
                        kind: PPTokenKind::Hash,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 1,
                    })
                }
            }
            b'+' => {
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'+' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::Increment,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'-' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::Decrement,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::MinusAssign,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'>' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'<' {
                    self.position += 1;
                    if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                        self.position += 1;
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
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'>' {
                    self.position += 1;
                    if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                        self.position += 1;
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
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'&' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::LogicAnd,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'|' {
                    self.position += 1;
                    Some(PPToken {
                        kind: PPTokenKind::LogicOr,
                        flags: PPTokenFlags::empty(),
                        location: SourceLoc::new(self.source_id, start_pos as u32),
                        length: 2,
                    })
                } else if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'=' {
                    self.position += 1;
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
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Tilde,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'.' => {
                self.position += 1;
                if self.position < self.buffer.len() && self.buffer[self.position] == b'.' &&
                   self.position + 1 < self.buffer.len() && self.buffer[self.position + 1] == b'.' {
                    self.position += 2;
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
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Question,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b':' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Colon,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b',' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Comma,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b';' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Semicolon,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'(' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::LeftParen,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b')' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::RightParen,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'[' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::LeftBracket,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b']' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::RightBracket,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'{' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::LeftBrace,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            b'}' => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::RightBrace,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
            _ => {
                self.position += 1;
                Some(PPToken {
                    kind: PPTokenKind::Unknown,
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc::new(self.source_id, start_pos as u32),
                    length: 1,
                })
            }
        }
    }

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

    fn lex_identifier(&mut self, start_pos: usize) -> PPToken {
        self.position += 1;
        while self.position < self.buffer.len() &&
              (self.buffer[self.position].is_ascii_alphanumeric() || self.buffer[self.position] == b'_') {
            self.position += 1;
        }

        let text = std::str::from_utf8(&self.buffer[start_pos..self.position]).unwrap();
        let symbol = Symbol::new(text);

        // Check for preprocessor keywords
        let kind = match text {
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
            _ => PPTokenKind::Identifier(symbol),
        };

        PPToken {
            kind,
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: (self.position - start_pos) as u16,
        }
    }

    fn lex_number(&mut self, start_pos: usize) -> PPToken {
        self.position += 1;
        while self.position < self.buffer.len() &&
              (self.buffer[self.position].is_ascii_digit() ||
               self.buffer[self.position] == b'.' ||
               self.buffer[self.position].is_ascii_alphabetic() ||
               self.buffer[self.position] == b'_') {
            self.position += 1;
        }

        let text = std::str::from_utf8(&self.buffer[start_pos..self.position]).unwrap();
        let value = text.parse::<i64>().unwrap_or(0);

        PPToken {
            kind: PPTokenKind::Number(value),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: (self.position - start_pos) as u16,
        }
    }

    fn lex_string_literal(&mut self, start_pos: usize) -> PPToken {
        self.position += 1;
        while self.position < self.buffer.len() && self.buffer[self.position] != b'"' {
            if self.buffer[self.position] == b'\\' && self.position + 1 < self.buffer.len() {
                self.position += 2;
            } else {
                self.position += 1;
            }
        }
        if self.position < self.buffer.len() {
            self.position += 1;
        }

        let text = std::str::from_utf8(&self.buffer[start_pos..self.position]).unwrap();
        let symbol = Symbol::new(text);

        PPToken {
            kind: PPTokenKind::StringLiteral(symbol),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: (self.position - start_pos) as u16,
        }
    }

    fn lex_char_literal(&mut self, start_pos: usize) -> PPToken {
        self.position += 1;
        while self.position < self.buffer.len() && self.buffer[self.position] != b'\'' {
            if self.buffer[self.position] == b'\\' && self.position + 1 < self.buffer.len() {
                self.position += 2;
            } else {
                self.position += 1;
            }
        }
        if self.position < self.buffer.len() {
            self.position += 1;
        }

        // Simplified: just return a placeholder value
        PPToken {
            kind: PPTokenKind::CharLiteral(0),
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(self.source_id, start_pos as u32),
            length: (self.position - start_pos) as u16,
        }
    }
}