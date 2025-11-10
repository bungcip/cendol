use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple as TargetInfo;

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

// Packed boolean flags for macro properties
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
    #[allow(unused)]
    if_loc: SourceLoc,
    was_skipping: bool,
    found_else: bool,
    found_non_skipping: bool,
}

/// Manages header search paths and include resolution
#[derive(Clone)]
pub struct HeaderSearch {
    #[allow(unused)]
    search_path: Vec<SearchPath>,
    #[allow(unused)]
    system_path: Vec<SearchPath>,
    #[allow(unused)]
    framework_path: Vec<SearchPath>,
    #[allow(unused)]
    quoted_includes: Vec<String>,
    #[allow(unused)]
    angled_includes: Vec<String>,
}

impl HeaderSearch {
    /// Resolve an include path to an absolute path
    pub fn resolve_path(&self, include_path: &str) -> Result<PathBuf, PreprocessorError> {
        // For now, just return the path as-is
        // In a full implementation, this would search through include paths
        Ok(PathBuf::from(include_path))
    }
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
    pub buffer_index: usize,   // Index into buffers Vec
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
    diag: &'src mut DiagnosticEngine,
    lang_opts: LangOptions,
    #[allow(unused)]
    target_info: TargetInfo,

    // Macro management
    macros: HashMap<Symbol, MacroInfo>,

    // Include management
    once_included: HashSet<SourceId>,

    // Conditional compilation state
    conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    include_stack: Vec<IncludeStackInfo>,
    header_search: HeaderSearch,

    // Token management
    #[allow(unused)]
    cur_token_lexer: Option<Box<PPTokenLexer>>,
    lexer_stack: Vec<PPLexer>,

    // State
    #[allow(unused)]
    in_main_file: bool,
    #[allow(unused)]
    is_parsing_main_file: bool,
    include_depth: usize,
    skipping: bool, // Whether we are currently skipping tokens due to conditional compilation
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
    put_back_token: Option<PPToken>,
    line_offset: usize,
    filename_override: Option<String>,
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
    #[error("#error directive: {0}")]
    ErrorDirective(String),
    #[error("Invalid conditional expression")]
    InvalidConditionalExpression,
    #[error("Unmatched #else")]
    UnmatchedElse,
    #[error("Unmatched #elif")]
    UnmatchedElif,
    #[error("#elif without #if")]
    ElifWithoutIf,
    #[error("#else without #if")]
    ElseWithoutIf,
    #[error("Macro expansion recursion detected")]
    MacroRecursion,
    #[error("Invalid token pasting")]
    InvalidTokenPasting,
    #[error("Invalid stringification")]
    InvalidStringification,
    #[error("Circular include detected")]
    CircularInclude,
}

impl<'src> Preprocessor<'src> {
    /// Create a new preprocessor
    pub fn new(
        source_manager: &'src mut SourceManager,
        diag: &'src mut DiagnosticEngine,
        lang_opts: LangOptions,
        target_info: TargetInfo,
        config: &PreprocessorConfig,
    ) -> Self {
        let header_search = HeaderSearch {
            search_path: config
                .system_include_paths
                .iter()
                .map(|p| SearchPath {
                    path: p.clone(),
                    is_system: true,
                })
                .collect(),
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
            once_included: HashSet::new(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            cur_token_lexer: None,
            lexer_stack: Vec::new(),
            in_main_file: true,
            is_parsing_main_file: true,
            include_depth: 0,
            skipping: false,
        };

        preprocessor.initialize_builtin_macros();
        preprocessor
    }

    /// Initialize built-in macros
    fn initialize_builtin_macros(&mut self) {
        let now: DateTime<Utc> = Utc::now();

        // __DATE__
        let date_str = format!(
            "\"{:02} {:02} {}\"",
            now.format("%b"),
            now.day(),
            now.year()
        );
        let date_tokens = self.tokenize_string(&date_str);
        self.define_builtin_macro("__DATE__", date_tokens);

        // __TIME__
        let time_str = format!(
            "\"{:02}:{:02}:{:02}\"",
            now.hour(),
            now.minute(),
            now.second()
        );
        let time_tokens = self.tokenize_string(&time_str);
        self.define_builtin_macro("__TIME__", time_tokens);

        // Other built-ins
        self.define_builtin_macro(
            "__STDC__",
            vec![PPToken {
                kind: PPTokenKind::Number(Symbol::new("1")),
                flags: PPTokenFlags::empty(),
                location: SourceLoc(0),
                length: 1,
            }],
        );

        if self.lang_opts.c11 {
            self.define_builtin_macro(
                "__STDC_VERSION__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("201112")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 6,
                }],
            );
            self.define_builtin_macro(
                "__STDC_HOSTED__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("1")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 1,
                }],
            );
            self.define_builtin_macro(
                "__STDC_MB_MIGHT_NEQ_WC__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("1")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 1,
                }],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("1")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 1,
                }],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559_COMPLEX__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("1")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 1,
                }],
            );
            self.define_builtin_macro(
                "__STDC_ISO_10646__",
                vec![PPToken {
                    kind: PPTokenKind::Number(Symbol::new("201103L")),
                    flags: PPTokenFlags::empty(),
                    location: SourceLoc(0),
                    length: 7,
                }],
            );
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
    pub fn process(
        &mut self,
        source_id: SourceId,
        _config: &PreprocessorConfig,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // Initialize lexer for main file
        let buffer = self.source_manager.get_buffer(source_id);
        let buffer_len = buffer.len() as u32;

        let lexer = PPLexer::new(source_id, buffer.to_vec());
        self.lexer_stack.push(lexer);

        let mut result_tokens = Vec::new();

        // Process tokens with string literal concatenation
        while let Some(token) = self.lex_token() {
            if self.is_currently_skipping() {
                // Skip tokens when in conditional compilation skip mode
                continue;
            }

            match token.kind {
                PPTokenKind::Hash if token.flags.contains(PPTokenFlags::STARTS_PP_LINE) => {
                    // Handle directive
                    self.handle_directive()?;
                }
                PPTokenKind::Identifier(_symbol) => {
                    // Check for macro expansion
                    if let Some(expanded) = self.expand_macro(&token)? {
                        // Add expanded tokens to result
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

        // Perform string literal concatenation
        result_tokens = self.concatenate_string_literals(result_tokens);

        // Add EOF token
        result_tokens.push(PPToken {
            kind: PPTokenKind::Eof,
            flags: PPTokenFlags::empty(),
            location: SourceLoc::new(source_id, buffer_len),
            length: 0,
        });

        Ok(result_tokens)
    }

    /// Get the current location from the lexer stack
    fn get_current_location(&self) -> SourceLoc {
        if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position as u32)
        } else {
            SourceLoc(0)
        }
    }

    /// Check if we are currently skipping tokens
    fn is_currently_skipping(&self) -> bool {
        self.skipping || self.conditional_stack.iter().any(|info| info.was_skipping)
    }

    /// Concatenate adjacent string literals (C11 6.4.5)
    fn concatenate_string_literals(&self, tokens: Vec<PPToken>) -> Vec<PPToken> {
        let mut result = Vec::new();
        let mut i = 0;
        
        while i < tokens.len() {
            if let PPTokenKind::StringLiteral(current_symbol) = tokens[i].kind {
                // Start collecting string literals
                let current_str = current_symbol.as_str();
                let mut concatenated_content = String::new();
                let start_location = tokens[i].location;
                
                // Get the content of the first string literal (removing quotes)
                if current_str.starts_with('"') && current_str.ends_with('"') {
                    let content = &current_str[1..current_str.len() - 1];
                    concatenated_content.push_str(content);
                } else {
                    // Invalid string literal format, just push as-is
                    result.push(tokens[i].clone());
                    i += 1;
                    continue;
                }
                
                // Look ahead for more string literals
                let mut j = i + 1;
                while j < tokens.len() {
                    if let PPTokenKind::StringLiteral(next_symbol) = tokens[j].kind {
                        let next_str = next_symbol.as_str();
                        if next_str.starts_with('"') && next_str.ends_with('"') {
                            let content = &next_str[1..next_str.len() - 1];
                            concatenated_content.push_str(content);
                            j += 1;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                
                // Create properly formatted concatenated string literal
                let final_string = format!("\"{}\"", concatenated_content);
                let concatenated_symbol = Symbol::new(&final_string);
                result.push(PPToken {
                    kind: PPTokenKind::StringLiteral(concatenated_symbol),
                    flags: tokens[i].flags,
                    location: start_location,
                    length: final_string.len() as u16,
                });
                
                i = j;
            } else {
                result.push(tokens[i].clone());
                i += 1;
            }
        }
        
        result
    }

    /// Set the skipping state
    fn set_skipping(&mut self, skipping: bool) {
        self.skipping = skipping;
    }

    /// Parse a conditional expression for #if and #elif
    fn parse_conditional_expression(&mut self) -> Result<Vec<PPToken>, PreprocessorError> {
        let mut tokens = Vec::new();
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        while let Some(token) = self.lex_token() {
            let token_line = if let Some(lexer) = self.lexer_stack.last() {
                lexer.get_line(token.location.0)
            } else {
                0
            };
            if token_line != start_line {
                // Put back the token from the next line
                if let Some(lexer) = self.lexer_stack.last_mut() {
                    lexer.put_back(token);
                }
                break;
            }
            tokens.push(token);
        }

        if tokens.is_empty() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }

        Ok(tokens)
    }

    /// Evaluate a conditional expression (simplified - just check if defined)
    fn evaluate_conditional_expression(
        &self,
        tokens: &[PPToken],
    ) -> Result<bool, PreprocessorError> {
        // Simplified evaluation: just check if the first token is defined
        if let Some(first_token) = tokens.first() {
            match &first_token.kind {
                PPTokenKind::Identifier(sym) => Ok(self.macros.contains_key(sym)),
                PPTokenKind::Number(sym) => {
                    // For now, treat numbers as true if non-zero
                    let text = sym.as_str();
                    Ok(text != "0")
                }
                _ => Err(PreprocessorError::InvalidConditionalExpression),
            }
        } else {
            Err(PreprocessorError::InvalidConditionalExpression)
        }
    }

    /// Skip a conditional compilation block when already skipping
    fn skip_conditional_block(&mut self) -> Result<(), PreprocessorError> {
        // For now, just skip to the end of the line
        // In a full implementation, this would need to handle nested conditionals
        while let Some(token) = self.lex_token() {
            if let Some(lexer) = self.lexer_stack.last() {
                let current_line = lexer.get_current_line();
                let token_line = lexer.get_line(token.location.0);
                if token_line != current_line {
                    // Put back the token from the next line
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    break;
                }
            }
        }
        Ok(())
    }

    /// Lex the next token
    fn lex_token(&mut self) -> Option<PPToken> {
        loop {
            if let Some(lexer) = self.lexer_stack.last_mut() {
                if let Some(token) = lexer.next_token() {
                    return Some(token);
                } else {
                    // EOF reached, pop the lexer
                    self.lexer_stack.pop();
                    if self.lexer_stack.is_empty() {
                        return None;
                    }
                    // Continue to try the next lexer in the stack
                }
            } else {
                return None;
            }
        }
    }

    /// Handle preprocessor directives
    fn handle_directive(&mut self) -> Result<(), PreprocessorError> {
        let token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;

        match token.kind {
            PPTokenKind::Define => self.handle_define()?,
            PPTokenKind::Undef => self.handle_undef()?,
            PPTokenKind::Include => self.handle_include()?,
            PPTokenKind::If => {
                if self.is_currently_skipping() {
                    // Skip the entire #if block
                    self.skip_conditional_block()?;
                } else {
                    let expr_tokens = self.parse_conditional_expression()?;
                    let condition = self.evaluate_conditional_expression(&expr_tokens)?;
                    self.handle_if_directive(condition)?;
                }
            }
            PPTokenKind::Ifdef => {
                if self.is_currently_skipping() {
                    self.skip_conditional_block()?;
                } else {
                    self.handle_ifdef()?;
                }
            }
            PPTokenKind::Ifndef => {
                if self.is_currently_skipping() {
                    self.skip_conditional_block()?;
                } else {
                    self.handle_ifndef()?;
                }
            }
            PPTokenKind::Elif => {
                if self.is_currently_skipping() {
                    self.skip_conditional_block()?;
                } else {
                    let expr_tokens = self.parse_conditional_expression()?;
                    let condition = self.evaluate_conditional_expression(&expr_tokens)?;
                    self.handle_elif_directive(condition)?;
                }
            }
            PPTokenKind::Else => {
                if self.is_currently_skipping() {
                    self.skip_conditional_block()?;
                } else {
                    self.handle_else()?;
                }
            }
            PPTokenKind::Endif => {
                if self.is_currently_skipping() {
                    self.skip_conditional_block()?;
                } else {
                    self.handle_endif()?;
                }
            }
            PPTokenKind::Line => self.handle_line()?,
            PPTokenKind::Pragma => self.handle_pragma()?,
            PPTokenKind::Error => self.handle_error()?,
            PPTokenKind::Warning => self.handle_warning()?,
            _ => {
                let diag = crate::diagnostic::Diagnostic {
                    level: crate::diagnostic::DiagnosticLevel::Error,
                    message: "Invalid preprocessor directive".to_string(),
                    location: SourceSpan::new(token.location, token.location),
                    code: Some("invalid_directive".to_string()),
                    hints: vec!["Valid directives include #define, #include, #if, #ifdef, #ifndef, #elif, #else, #endif, #line, #pragma, #error, #warning".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Err(PreprocessorError::InvalidDirective);
            }
        }

        Ok(())
    }

    /// Handle #define directive
    fn handle_define(&mut self) -> Result<(), PreprocessorError> {
        let name_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PreprocessorError::ExpectedIdentifier),
        };

        // Check for macro redefinition
        if let Some(existing) = self.macros.get(&name)
            && !existing.flags.contains(MacroFlags::BUILTIN)
        {
            // Emit warning for redefinition
            let diag = crate::diagnostic::Diagnostic {
                level: crate::diagnostic::DiagnosticLevel::Warning,
                message: format!("Redefinition of macro '{}'", name.as_str()),
                location: SourceSpan::new(name_token.location, name_token.location),
                code: Some("macro_redefinition".to_string()),
                hints: Vec::new(),
                related: vec![SourceSpan::new(existing.location, existing.location)],
            };
            self.diag.report_diagnostic(diag);
        }

        let mut flags = MacroFlags::empty();
        let mut params = Vec::new();
        let mut variadic = None;
        let next = self.lex_token();
        if let Some(token) = next {
            if token.kind == PPTokenKind::LeftParen {
                flags |= MacroFlags::FUNCTION_LIKE;
                // parse params
                loop {
                    let param_token = self
                        .lex_token()
                        .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
                    match param_token.kind {
                        PPTokenKind::RightParen => break,
                        PPTokenKind::Identifier(sym) => {
                            if params.contains(&sym) {
                                return Err(PreprocessorError::InvalidMacroParameter);
                            }
                            params.push(sym);
                            let sep = self
                                .lex_token()
                                .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
                            match sep.kind {
                                PPTokenKind::Comma => continue,
                                PPTokenKind::RightParen => break,
                                PPTokenKind::Ellipsis => {
                                    variadic = Some(sym);
                                    flags |= MacroFlags::C99_VARARGS;
                                    let rparen = self
                                        .lex_token()
                                        .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
                                    if rparen.kind != PPTokenKind::RightParen {
                                        return Err(PreprocessorError::InvalidMacroParameter);
                                    }
                                    break;
                                }
                                _ => return Err(PreprocessorError::InvalidMacroParameter),
                            }
                        }
                        PPTokenKind::Ellipsis => {
                            flags |= MacroFlags::GNU_VARARGS;
                            variadic = Some(Symbol::new("__VA_ARGS__"));
                            let rparen = self
                                .lex_token()
                                .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
                            if rparen.kind != PPTokenKind::RightParen {
                                return Err(PreprocessorError::InvalidMacroParameter);
                            }
                            break;
                        }
                        _ => return Err(PreprocessorError::InvalidMacroParameter),
                    }
                }
            } else if let Some(lexer) = self.lexer_stack.last_mut() {
                lexer.put_back(token);
            }
        }
        // Now, collect replacement tokens
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };
        let mut tokens = Vec::new();
        while let Some(token) = self.lex_token() {
            let token_line = if let Some(lexer) = self.lexer_stack.last() {
                lexer.get_line(token.location.0)
            } else {
                0
            };
            if token_line != start_line {
                if let Some(lexer) = self.lexer_stack.last_mut() {
                    lexer.put_back(token);
                }
                break;
            }
            tokens.push(token);
        }
        // Store the macro
        let macro_info = MacroInfo {
            location: name_token.location,
            flags,
            tokens,
            parameter_list: params,
            variadic_arg: variadic,
        };
        self.macros.insert(name, macro_info);
        Ok(())
    }
    fn handle_undef(&mut self) -> Result<(), PreprocessorError> {
        let name_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PreprocessorError::ExpectedIdentifier),
        };
        // Remove the macro from the table if it exists
        self.macros.remove(&name);
        Ok(())
    }
    fn handle_include(&mut self) -> Result<(), PreprocessorError> {
        // Parse the include path
        let token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let path_str = match token.kind {
            PPTokenKind::StringLiteral(symbol) => {
                // Remove quotes from string literal
                let full_str = symbol.as_str();
                if full_str.starts_with('"') && full_str.ends_with('"') {
                    full_str[1..full_str.len() - 1].to_string()
                } else {
                    return Err(PreprocessorError::InvalidIncludePath);
                }
            }
            PPTokenKind::Less => {
                // Angled include: collect tokens until >
                let mut path_parts = Vec::new();
                loop {
                    let part_token = self
                        .lex_token()
                        .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
                    match part_token.kind {
                        PPTokenKind::Greater => break,
                        _ => path_parts.push(part_token),
                    }
                }
                // Concatenate the path parts
                let mut path = String::new();
                for (i, part) in path_parts.iter().enumerate() {
                    if i > 0 {
                        path.push(' ');
                    }
                    let buffer = self.source_manager.get_buffer(part.location.source_id());
                    let start = part.location.offset() as usize;
                    let end = start + part.length as usize;
                    if end <= buffer.len() {
                        let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                        path.push_str(text);
                    }
                }
                path
            }
            _ => return Err(PreprocessorError::InvalidIncludePath),
        };

        // Check include depth
        if self.include_depth >= 200 {
            // Arbitrary limit
            return Err(PreprocessorError::IncludeDepthExceeded);
        }

        // Check for circular includes
        if self.include_stack.iter().any(|info| {
            let file_info = self.source_manager.get_file_info(info.file_id);
            file_info.is_some_and(|fi| fi.path == path_str)
        }) {
            return Err(PreprocessorError::CircularInclude);
        }

        // Resolve the path
        let resolved_path = self.header_search.resolve_path(&path_str)?;

        // Load the file
        let include_source_id = self
            .source_manager
            .add_file_from_path(&resolved_path)
            .map_err(|_| {
                // Emit diagnostic for file not found
                let diag = crate::diagnostic::Diagnostic {
                    level: crate::diagnostic::DiagnosticLevel::Error,
                    message: format!("Include file '{}' not found", path_str),
                    location: SourceSpan::new(token.location, token.location),
                    code: Some("include_file_not_found".to_string()),
                    hints: vec!["Check the include path and ensure the file exists".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                PreprocessorError::FileNotFound
            })?;

        // Check if file has #pragma once
        if self.once_included.contains(&include_source_id) {
            // Skip including this file again
            return Ok(());
        }

        // Push to include stack
        self.include_stack.push(IncludeStackInfo {
            file_id: include_source_id,
            location: token.location,
        });

        // Create lexer for the included file
        let buffer = self.source_manager.get_buffer(include_source_id);
        let lexer = PPLexer::new(include_source_id, buffer.to_vec());
        self.lexer_stack.push(lexer);

        self.include_depth += 1;

        Ok(())
    }
    fn handle_if_directive(&mut self, condition: bool) -> Result<(), PreprocessorError> {
        // Push new conditional state
        let info = PPConditionalInfo {
            if_loc: self.get_current_location(),
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: false,
        };
        self.conditional_stack.push(info);

        // Set skipping state based on condition
        if !condition {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_ifdef(&mut self) -> Result<(), PreprocessorError> {
        let name_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PreprocessorError::ExpectedIdentifier),
        };

        let defined = self.macros.contains_key(&name);
        let info = PPConditionalInfo {
            if_loc: self.get_current_location(),
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: false,
        };
        self.conditional_stack.push(info);

        if !defined {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_ifndef(&mut self) -> Result<(), PreprocessorError> {
        let name_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PreprocessorError::ExpectedIdentifier),
        };

        let defined = self.macros.contains_key(&name);
        let info = PPConditionalInfo {
            if_loc: self.get_current_location(),
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: false,
        };
        self.conditional_stack.push(info);

        if defined {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_elif_directive(&mut self, condition: bool) -> Result<(), PreprocessorError> {
        if self.conditional_stack.is_empty() {
            return Err(PreprocessorError::ElifWithoutIf);
        }

        let current = self.conditional_stack.last_mut().unwrap();
        if current.found_else {
            return Err(PreprocessorError::UnmatchedElif);
        }

        // Determine if we should start processing
        let should_process = !current.found_non_skipping && condition;

        if should_process {
            current.found_non_skipping = true;
            self.set_skipping(false);
        } else {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_else(&mut self) -> Result<(), PreprocessorError> {
        if self.conditional_stack.is_empty() {
            return Err(PreprocessorError::ElseWithoutIf);
        }

        let current = self.conditional_stack.last_mut().unwrap();
        if current.found_else {
            return Err(PreprocessorError::UnmatchedElse);
        }
        current.found_else = true;

        // Process else block if no previous branch was taken
        let should_process = !current.found_non_skipping;
        if should_process {
            self.set_skipping(false);
        } else {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_endif(&mut self) -> Result<(), PreprocessorError> {
        if self.conditional_stack.is_empty() {
            return Err(PreprocessorError::UnmatchedEndif);
        }

        let info = self.conditional_stack.pop().unwrap();
        // Restore previous skipping state
        self.set_skipping(info.was_skipping);

        Ok(())
    }
    fn handle_line(&mut self) -> Result<(), PreprocessorError> {
        // Parse line number
        let line_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        let line_number = match line_token.kind {
            PPTokenKind::Number(symbol) => {
                let text = symbol.as_str();
                text.parse::<usize>()
                    .map_err(|_| PreprocessorError::InvalidDirective)?
            }
            _ => return Err(PreprocessorError::InvalidDirective),
        };

        // Optional filename
        let mut filename = None;
        if let Some(token) = self.lex_token() {
            match token.kind {
                PPTokenKind::StringLiteral(symbol) => {
                    let full_str = symbol.as_str();
                    if full_str.starts_with('"') && full_str.ends_with('"') {
                        filename = Some(full_str[1..full_str.len() - 1].to_string());
                    } else {
                        return Err(PreprocessorError::InvalidDirective);
                    }
                }
                _ => {
                    // Put back the token if it's not a string literal
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                }
            }
        }

        // Update lexer state
        if let Some(lexer) = self.lexer_stack.last_mut() {
            lexer.line_offset = line_number.saturating_sub(lexer.get_current_line() + 1);
            lexer.filename_override = filename;
        }

        Ok(())
    }
    fn handle_pragma(&mut self) -> Result<(), PreprocessorError> {
        // Parse the pragma directive
        let pragma_token = self
            .lex_token()
            .ok_or(PreprocessorError::UnexpectedEndOfFile)?;
        match pragma_token.kind {
            PPTokenKind::Identifier(symbol) => {
                let pragma_name = symbol.as_str();
                if pragma_name == "once" {
                    // Mark the current file as once-included
                    if let Some(lexer) = self.lexer_stack.last() {
                        self.once_included.insert(lexer.source_id);
                    }
                }
                // For now, ignore other pragmas
            }
            _ => {
                // Invalid pragma, but we'll ignore it for now
            }
        }
        // Skip to end of line
        while let Some(token) = self.lex_token() {
            if let Some(lexer) = self.lexer_stack.last() {
                let current_line = lexer.get_current_line();
                let token_line = lexer.get_line(token.location.0);
                if token_line != current_line {
                    // Put back the token from the next line
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    break;
                }
            }
        }
        Ok(())
    }

    fn handle_error(&mut self) -> Result<(), PreprocessorError> {
        // Collect the error message from the rest of the line
        let mut message_parts = Vec::new();
        while let Some(token) = self.lex_token() {
            if let Some(lexer) = self.lexer_stack.last() {
                let current_line = lexer.get_current_line();
                let token_line = lexer.get_line(token.location.0);
                if token_line != current_line {
                    // Put back the token from the next line
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    break;
                }
            }
            // Get token text
            let buffer = self.source_manager.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end <= buffer.len() {
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                message_parts.push(text.to_string());
            }
        }
        let message = message_parts.join(" ");
        Err(PreprocessorError::ErrorDirective(message))
    }

    fn handle_warning(&mut self) -> Result<(), PreprocessorError> {
        // Collect the warning message from the rest of the line
        let mut message_parts = Vec::new();
        let directive_location = if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position as u32)
        } else {
            SourceLoc(0)
        };
        while let Some(token) = self.lex_token() {
            if let Some(lexer) = self.lexer_stack.last() {
                let current_line = lexer.get_current_line();
                let token_line = lexer.get_line(token.location.0);
                if token_line != current_line {
                    // Put back the token from the next line
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    break;
                }
            }
            // Get token text
            let buffer = self.source_manager.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end <= buffer.len() {
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                message_parts.push(text.to_string());
            }
        }
        let message = message_parts.join(" ");
        // For warning, we emit a diagnostic but don't stop compilation
        let diag = crate::diagnostic::Diagnostic {
            level: crate::diagnostic::DiagnosticLevel::Warning,
            message,
            location: SourceSpan::new(directive_location, directive_location),
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diag.report_diagnostic(diag);
        Ok(())
    }

    /// Expand a macro if it exists
    fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PreprocessorError> {
        if let PPTokenKind::Identifier(symbol) = token.kind {
            // Check if macro exists and is not disabled
            let macro_info = match self.macros.get(&symbol) {
                Some(m) if !m.flags.contains(MacroFlags::DISABLED) => m.clone(),
                _ => return Ok(None),
            };

            // Check for recursion
            if macro_info.flags.contains(MacroFlags::DISABLED) {
                return Err(PreprocessorError::MacroRecursion);
            }

            // Mark as used
            if let Some(m) = self.macros.get_mut(&symbol) {
                m.flags |= MacroFlags::USED;
            }

            // Temporarily disable the macro to prevent infinite recursion
            if let Some(m) = self.macros.get_mut(&symbol) {
                m.flags |= MacroFlags::DISABLED;
            }

            let result = if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
                self.expand_function_macro(&macro_info, token)
            } else {
                self.expand_object_macro(&macro_info, token)
            };

            // Re-enable the macro
            if let Some(m) = self.macros.get_mut(&symbol) {
                m.flags.remove(MacroFlags::DISABLED);
            }

            result.map(Some)
        } else {
            Ok(None)
        }
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        _token: &PPToken,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // Clone tokens and rescan for further expansion
        let mut expanded = macro_info.tokens.clone();
        self.expand_tokens(&mut expanded)?;
        Ok(expanded)
    }

    /// Expand a function-like macro
    fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        _token: &PPToken,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // Parse arguments from lexer
        let args = self.parse_macro_args_from_lexer(macro_info)?;

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args)?;

        // Rescan for further expansion
        let mut expanded = substituted;
        self.expand_tokens(&mut expanded)?;

        Ok(expanded)
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(
        &mut self,
        macro_info: &MacroInfo,
    ) -> Result<Vec<Vec<PPToken>>, PreprocessorError> {
        // Skip whitespace and expect '('
        let mut found_lparen = false;
        while let Some(token) = self.lex_token() {
            match token.kind {
                PPTokenKind::LeftParen => {
                    found_lparen = true;
                    break;
                }
                PPTokenKind::Eof => return Err(PreprocessorError::UnexpectedEndOfFile),
                _ if token.flags.contains(PPTokenFlags::LEADING_SPACE) => continue,
                _ => {
                    // Put back non-whitespace token
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    return Err(PreprocessorError::InvalidMacroParameter);
                }
            }
        }

        if !found_lparen {
            return Err(PreprocessorError::UnexpectedEndOfFile);
        }

        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut paren_depth = 0;
        let mut brace_depth = 0;
        let mut bracket_depth = 0;

        while let Some(token) = self.lex_token() {
            match token.kind {
                PPTokenKind::LeftParen => {
                    paren_depth += 1;
                    current_arg.push(token);
                }
                PPTokenKind::RightParen => {
                    if paren_depth == 0 {
                        // End of arguments
                        if !current_arg.is_empty() || !args.is_empty() {
                            args.push(current_arg);
                        }
                        break;
                    }
                    paren_depth -= 1;
                    current_arg.push(token);
                }
                PPTokenKind::LeftBrace => {
                    brace_depth += 1;
                    current_arg.push(token);
                }
                PPTokenKind::RightBrace => {
                    brace_depth -= 1;
                    current_arg.push(token);
                }
                PPTokenKind::LeftBracket => {
                    bracket_depth += 1;
                    current_arg.push(token);
                }
                PPTokenKind::RightBracket => {
                    bracket_depth -= 1;
                    current_arg.push(token);
                }
                PPTokenKind::Comma
                    if paren_depth == 0 && brace_depth == 0 && bracket_depth == 0 =>
                {
                    // Argument separator
                    args.push(current_arg);
                    current_arg = Vec::new();
                }
                _ => {
                    current_arg.push(token);
                }
            }
        }

        // Validate argument count
        let expected_args = macro_info.parameter_list.len();
        let has_variadic = macro_info.variadic_arg.is_some();

        if has_variadic {
            if args.len() < expected_args {
                let diag = crate::diagnostic::Diagnostic {
                    level: crate::diagnostic::DiagnosticLevel::Error,
                    message: format!(
                        "Too few arguments for macro '{}': expected at least {}, got {}",
                        macro_info
                            .parameter_list
                            .iter()
                            .map(|s| s.as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                        expected_args,
                        args.len()
                    ),
                    location: SourceSpan::new(macro_info.location, macro_info.location),
                    code: Some("macro_too_few_args".to_string()),
                    hints: Vec::new(),
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Err(PreprocessorError::InvalidMacroParameter);
            }
        } else if args.len() != expected_args {
            let diag = crate::diagnostic::Diagnostic {
                level: crate::diagnostic::DiagnosticLevel::Error,
                message: format!(
                    "Wrong number of arguments for macro '{}': expected {}, got {}",
                    macro_info
                        .parameter_list
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", "),
                    expected_args,
                    args.len()
                ),
                location: SourceSpan::new(macro_info.location, macro_info.location),
                code: Some("macro_wrong_arg_count".to_string()),
                hints: Vec::new(),
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PreprocessorError::InvalidMacroParameter);
        }

        Ok(args)
    }

    /// Substitute parameters in macro body
    fn substitute_macro(
        &mut self,
        macro_info: &MacroInfo,
        args: &[Vec<PPToken>],
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < macro_info.tokens.len() {
            let token = &macro_info.tokens[i];

            match token.kind {
                PPTokenKind::Hash => {
                    // Stringification operator
                    if i + 1 < macro_info.tokens.len() {
                        let next_token = &macro_info.tokens[i + 1];
                        if let PPTokenKind::Identifier(param_symbol) = next_token.kind {
                            if let Some(param_index) = macro_info
                                .parameter_list
                                .iter()
                                .position(|&p| p == param_symbol)
                            {
                                let arg_tokens = &args[param_index];
                                let stringified =
                                    self.stringify_tokens(arg_tokens, token.location)?;
                                result.push(stringified);
                                i += 2;
                                continue;
                            } else if macro_info.variadic_arg == Some(param_symbol) {
                                // Handle variadic argument
                                let start_index = macro_info.parameter_list.len();
                                let variadic_args = args
                                    .iter()
                                    .skip(start_index)
                                    .flatten()
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let stringified =
                                    self.stringify_tokens(&variadic_args, token.location)?;
                                result.push(stringified);
                                i += 2;
                                continue;
                            }
                        }
                    }
                    result.push(token.clone());
                }
                PPTokenKind::HashHash => {
                    // Token pasting operator
                    if !result.is_empty() && i + 1 < macro_info.tokens.len() {
                        let left = result.pop().unwrap();
                        let right = &macro_info.tokens[i + 1];
                        let pasted = self.paste_tokens(&left, right)?;
                        result.extend(pasted);
                        i += 2;
                        continue;
                    }
                    result.push(token.clone());
                }
                PPTokenKind::Identifier(symbol) => {
                    // Parameter substitution
                    if let Some(param_index) =
                        macro_info.parameter_list.iter().position(|&p| p == symbol)
                    {
                        result.extend(args[param_index].clone());
                    } else if macro_info.variadic_arg == Some(symbol) {
                        // Handle variadic argument
                        let start_index = macro_info.parameter_list.len();
                        let mut first = true;
                        for arg in args.iter().skip(start_index) {
                            if !first {
                                result.push(PPToken {
                                    kind: PPTokenKind::Comma,
                                    flags: PPTokenFlags::empty(),
                                    location: token.location,
                                    length: 1,
                                });
                            }
                            result.extend(arg.clone());
                            first = false;
                        }
                    } else {
                        result.push(token.clone());
                    }
                }
                _ => {
                    result.push(token.clone());
                }
            }
            i += 1;
        }

        Ok(result)
    }

    /// Stringify tokens for # operator
    fn stringify_tokens(
        &self,
        tokens: &[PPToken],
        location: SourceLoc,
    ) -> Result<PPToken, PreprocessorError> {
        let mut result = String::new();
        result.push('"');

        for (i, token) in tokens.iter().enumerate() {
            if i > 0 {
                // Add space between tokens
                result.push(' ');
            }

            // Get token text from source manager
            let buffer = self.source_manager.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end <= buffer.len() {
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                // Escape quotes and backslashes in the text
                for ch in text.chars() {
                    match ch {
                        '"' => result.push_str("\\\""),
                        '\\' => result.push_str("\\\\"),
                        _ => result.push(ch),
                    }
                }
            } else {
                return Err(PreprocessorError::InvalidStringification);
            }
        }

        result.push('"');

        Ok(PPToken {
            kind: PPTokenKind::StringLiteral(Symbol::new(&result)),
            flags: PPTokenFlags::empty(),
            location,
            length: result.len() as u16,
        })
    }

    /// Paste tokens for ## operator
    fn paste_tokens(
        &self,
        left: &PPToken,
        right: &PPToken,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // Get text of both tokens
        let left_buffer = self.source_manager.get_buffer(left.location.source_id());
        let left_start = left.location.offset() as usize;
        let left_end = left_start + left.length as usize;
        let left_text = if left_end <= left_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&left_buffer[left_start..left_end]) }
        } else {
            return Err(PreprocessorError::InvalidTokenPasting);
        };

        let right_buffer = self.source_manager.get_buffer(right.location.source_id());
        let right_start = right.location.offset() as usize;
        let right_end = right_start + right.length as usize;
        let right_text = if right_end <= right_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&right_buffer[right_start..right_end]) }
        } else {
            return Err(PreprocessorError::InvalidTokenPasting);
        };

        let pasted_text = format!("{}{}", left_text, right_text);

        // Try to lex the pasted text as a single token
        // For simplicity, we'll create an identifier token
        // In a full implementation, this would need proper lexing
        let symbol = Symbol::new(&pasted_text);

        Ok(vec![PPToken {
            kind: PPTokenKind::Identifier(symbol),
            flags: PPTokenFlags::empty(),
            location: left.location, // Use left token's location
            length: pasted_text.len() as u16,
        }])
    }

    /// Expand tokens by rescanning for further macro expansion
    fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>) -> Result<(), PreprocessorError> {
        let mut i = 0;
        while i < tokens.len() {
            if let PPTokenKind::Identifier(_symbol) = tokens[i].kind
                && let Some(expanded) = self.expand_macro(&tokens[i])?
            {
                // Replace current token with expanded tokens
                tokens.splice(i..i + 1, expanded);
                // Don't increment i, rescan from current position
                continue;
            }
            i += 1;
        }
        Ok(())
    }
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

    pub fn next_token(&mut self) -> Option<PPToken> {
        if let Some(token) = self.put_back_token.take() {
            return Some(token);
        }

        self.skip_whitespace_and_comments();

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
                let is_start_of_line = start_pos == *self.line_starts.last().unwrap_or(&0) as usize;
                let mut flags = PPTokenFlags::empty();
                if is_start_of_line {
                    flags |= PPTokenFlags::STARTS_PP_LINE;
                }
                if self.position < self.buffer.len() && self.buffer[self.position] == b'#' {
                    self.position += 1;
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
                if self.position < self.buffer.len()
                    && self.buffer[self.position] == b'.'
                    && self.position + 1 < self.buffer.len()
                    && self.buffer[self.position + 1] == b'.'
                {
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

    fn lex_identifier(&mut self, start_pos: usize) -> PPToken {
        self.position += 1;
        while self.position < self.buffer.len()
            && (self.buffer[self.position].is_ascii_alphanumeric()
                || self.buffer[self.position] == b'_')
        {
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
            "error" => PPTokenKind::Error,
            "warning" => PPTokenKind::Warning,
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
        while self.position < self.buffer.len()
            && (self.buffer[self.position].is_ascii_digit()
                || self.buffer[self.position] == b'.'
                || self.buffer[self.position].is_ascii_alphabetic()
                || self.buffer[self.position] == b'_')
        {
            self.position += 1;
        }

        let text = std::str::from_utf8(&self.buffer[start_pos..self.position]).unwrap();
        let symbol = Symbol::new(text);

        PPToken {
            kind: PPTokenKind::Number(symbol),
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

    fn put_back(&mut self, token: PPToken) {
        self.put_back_token = Some(token);
    }

    fn get_line(&self, offset: u32) -> usize {
        self.line_starts.partition_point(|&x| x <= offset) - 1
    }

    fn get_current_line(&self) -> usize {
        self.line_starts.len() - 1 + self.line_offset
    }
}
