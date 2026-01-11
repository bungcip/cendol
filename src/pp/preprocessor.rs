use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::intern::StringId;
use crate::lang_options::LangOptions;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use hashbrown::HashMap;
use std::collections::{HashSet, VecDeque};

use super::pp_lexer::PPLexer;
use crate::pp::interpreter::Interpreter;
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use std::path::{Path, PathBuf};
use target_lexicon::{Architecture, OperatingSystem, Triple};

/// Preprocessor directive kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Define,
    Undef,
    Include,
    If,
    Ifdef,
    Ifndef,
    Elif,
    Else,
    Endif,
    Line,
    Pragma,
    Error,
    Warning,
}

/// Table of pre-interned preprocessor directive names for O(1) keyword recognition
#[derive(Clone)]
pub(crate) struct DirectiveKeywordTable {
    define: StringId,
    undef: StringId,
    include: StringId,
    if_: StringId,
    ifdef: StringId,
    ifndef: StringId,
    elif: StringId,
    else_: StringId,
    endif: StringId,
    line: StringId,
    pragma: StringId,
    error: StringId,
    warning: StringId,
    defined: StringId, // For the defined operator in expressions
}

impl Default for DirectiveKeywordTable {
    fn default() -> Self {
        Self::new()
    }
}

impl DirectiveKeywordTable {
    pub(crate) fn new() -> Self {
        DirectiveKeywordTable {
            define: StringId::new("define"),
            undef: StringId::new("undef"),
            include: StringId::new("include"),
            if_: StringId::new("if"),
            ifdef: StringId::new("ifdef"),
            ifndef: StringId::new("ifndef"),
            elif: StringId::new("elif"),
            else_: StringId::new("else"),
            endif: StringId::new("endif"),
            line: StringId::new("line"),
            pragma: StringId::new("pragma"),
            error: StringId::new("error"),
            warning: StringId::new("warning"),
            defined: StringId::new("defined"),
        }
    }

    pub(crate) fn is_directive(&self, symbol: StringId) -> Option<DirectiveKind> {
        if symbol == self.define {
            Some(DirectiveKind::Define)
        } else if symbol == self.undef {
            Some(DirectiveKind::Undef)
        } else if symbol == self.include {
            Some(DirectiveKind::Include)
        } else if symbol == self.if_ {
            Some(DirectiveKind::If)
        } else if symbol == self.ifdef {
            Some(DirectiveKind::Ifdef)
        } else if symbol == self.ifndef {
            Some(DirectiveKind::Ifndef)
        } else if symbol == self.elif {
            Some(DirectiveKind::Elif)
        } else if symbol == self.else_ {
            Some(DirectiveKind::Else)
        } else if symbol == self.endif {
            Some(DirectiveKind::Endif)
        } else if symbol == self.line {
            Some(DirectiveKind::Line)
        } else if symbol == self.pragma {
            Some(DirectiveKind::Pragma)
        } else if symbol == self.error {
            Some(DirectiveKind::Error)
        } else if symbol == self.warning {
            Some(DirectiveKind::Warning)
        } else {
            None
        }
    }

    /// Get the interned symbol for the "defined" operator
    pub(crate) fn defined_symbol(&self) -> StringId {
        self.defined
    }
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
pub(crate) struct MacroInfo {
    pub(crate) location: SourceLoc,
    pub(crate) flags: MacroFlags, // Packed boolean flags
    pub(crate) tokens: Vec<PPToken>,
    pub(crate) parameter_list: Vec<StringId>,
    pub(crate) variadic_arg: Option<StringId>,
}

/// Represents conditional compilation state
#[derive(Debug, Clone)]
pub struct PPConditionalInfo {
    was_skipping: bool,
    found_else: bool,
    found_non_skipping: bool,
}

/// Manages header search paths and include resolution
#[derive(Clone)]
pub(crate) struct HeaderSearch {
    #[allow(unused)]
    search_path: Vec<SearchPath>,
    system_path: Vec<SearchPath>,
    framework_path: Vec<SearchPath>,
    quoted_includes: Vec<String>,
    angled_includes: Vec<String>,
}

impl HeaderSearch {
    /// Add a system include path
    pub(crate) fn add_system_path(&mut self, path: PathBuf) {
        self.system_path.push(SearchPath {
            path, /* , is_system: true */
        });
    }

    /// Add a quoted include path (-iquote)
    pub(crate) fn add_quoted_path(&mut self, path: PathBuf) {
        self.quoted_includes.push(path.to_string_lossy().to_string());
    }

    /// Add an angled include path (-I)
    pub(crate) fn add_angled_path(&mut self, path: PathBuf) {
        self.angled_includes.push(path.to_string_lossy().to_string());
    }

    /// Add a framework path
    pub(crate) fn add_framework_path(&mut self, path: PathBuf) {
        self.framework_path.push(SearchPath {
            path, /* , is_system: true */
        });
    }

    /// Resolve an include path to an absolute path
    pub(crate) fn resolve_path(&self, include_path: &str, is_angled: bool, current_dir: &Path) -> Option<PathBuf> {
        if is_angled {
            // Angled includes: search angled_includes, then system_path, then framework_path
            for include_path_str in &self.angled_includes {
                let candidate = Path::new(include_path_str).join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
            for search_path in &self.system_path {
                let candidate = search_path.path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
            for search_path in &self.framework_path {
                let candidate = search_path.path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        } else {
            // Quoted includes: search current_dir, then quoted_includes, then angled_includes, then system_path, then framework_path
            let candidate = current_dir.join(include_path);
            if candidate.exists() {
                return Some(candidate);
            }
            for include_path_str in &self.quoted_includes {
                let candidate = Path::new(include_path_str).join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
            for include_path_str in &self.angled_includes {
                let candidate = Path::new(include_path_str).join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
            for search_path in &self.system_path {
                let candidate = search_path.path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
            for search_path in &self.framework_path {
                let candidate = search_path.path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        }
        None
    }
}

#[derive(Clone)]
pub(crate) struct SearchPath {
    pub(crate) path: PathBuf,
    // pub is_system: bool,
}

/// Include stack information
#[derive(Clone)]
pub(crate) struct IncludeStackInfo {
    pub(crate) file_id: SourceId,
    // pub location: SourceLoc,
}

/// Configuration for preprocessor
#[derive(Debug, Clone)]
pub struct PPConfig {
    pub max_include_depth: usize,
    pub system_include_paths: Vec<PathBuf>,
    pub quoted_include_paths: Vec<PathBuf>,
    pub angled_include_paths: Vec<PathBuf>,
    pub framework_paths: Vec<PathBuf>,
    pub lang_options: LangOptions,
    pub target: Triple,
}

impl Default for PPConfig {
    fn default() -> Self {
        Self {
            max_include_depth: 200,
            system_include_paths: Vec::new(),
            quoted_include_paths: Vec::new(),
            angled_include_paths: Vec::new(),
            framework_paths: Vec::new(),
            lang_options: LangOptions::default(),
            target: Triple::host(),
        }
    }
}

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    source_manager: &'src mut SourceManager,
    diag: &'src mut DiagnosticEngine,
    lang_opts: LangOptions,
    target: Triple,

    // Pre-interned directive keywords for fast comparison
    directive_keywords: DirectiveKeywordTable,

    // Macro management
    macros: HashMap<StringId, MacroInfo>,

    // Include management
    once_included: HashSet<SourceId>,

    // Conditional compilation state
    conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    include_stack: Vec<IncludeStackInfo>,
    header_search: HeaderSearch,
    built_in_headers: HashMap<&'static str, &'static str>,

    // Token management
    lexer_stack: Vec<PPLexer>,
    pending_tokens: VecDeque<PPToken>,

    // State
    include_depth: usize,
    max_include_depth: usize,
    counter: u32,
}

/// Preprocessor errors
#[derive(Debug, thiserror::Error)]
pub enum PPError {
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
    InvalidMacroParameter { span: SourceSpan },
    #[error("Invalid include path")]
    InvalidIncludePath,
    #[error("Unmatched #endif")]
    UnmatchedEndif,
    #[error("#error directive: {0}")]
    ErrorDirective(String),
    #[error("Invalid conditional expression")]
    InvalidConditionalExpression,
    #[error("Invalid #line directive")]
    InvalidLineDirective,
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
    #[error("Expected end of directive")]
    ExpectedEod,
    #[error("Unknown pragma: {0}")]
    UnknownPragma(String),
}

impl PPError {
    pub(crate) fn span(&self) -> SourceSpan {
        match self {
            PPError::InvalidMacroParameter { span } => *span,
            _ => SourceSpan::new(SourceLoc::builtin(), SourceLoc::builtin()),
        }
    }
}

impl From<PPError> for Diagnostic {
    fn from(val: PPError) -> Self {
        let level = match &val {
            PPError::ErrorDirective(_) => DiagnosticLevel::Error,
            PPError::UnknownPragma(_) => DiagnosticLevel::Error,
            _ => DiagnosticLevel::Error,
        };

        Diagnostic {
            level,
            message: val.to_string(),
            span: val.span(),
            ..Default::default()
        }
    }
}

impl<'src> Preprocessor<'src> {
    /// Create a new preprocessor
    pub fn new(source_manager: &'src mut SourceManager, diag: &'src mut DiagnosticEngine, config: &PPConfig) -> Self {
        let mut header_search = HeaderSearch {
            search_path: config
                .system_include_paths
                .iter()
                .map(|p| SearchPath {
                    path: p.clone(),
                    // is_system: true,
                })
                .collect(),
            system_path: Vec::new(),
            framework_path: Vec::new(),
            quoted_includes: Vec::new(),
            angled_includes: Vec::new(),
        };

        // Populate the new fields
        for path in &config.system_include_paths {
            header_search.add_system_path(path.clone());
        }
        for path in &config.quoted_include_paths {
            header_search.add_quoted_path(path.clone());
        }
        for path in &config.angled_include_paths {
            header_search.add_angled_path(path.clone());
        }
        for path in &config.framework_paths {
            header_search.add_framework_path(path.clone());
        }

        let mut built_in_headers = HashMap::new();
        built_in_headers.insert("stddef.h", include_str!("../../custom-include/stddef.h"));
        built_in_headers.insert("stdint.h", include_str!("../../custom-include/stdint.h"));
        built_in_headers.insert("stdarg.h", include_str!("../../custom-include/stdarg.h"));
        built_in_headers.insert("stdbool.h", include_str!("../../custom-include/stdbool.h"));

        // built_in_headers.insert("stdlib.h", include_str!("../../custom-include/stdlib.h"));
        // built_in_headers.insert("wchar.h", include_str!("../../custom-include/wchar.h"));
        // built_in_headers.insert("stdio.h", include_str!("../../custom-include/stdio.h"));

        let mut preprocessor = Preprocessor {
            source_manager,
            diag,
            lang_opts: config.lang_options,
            directive_keywords: DirectiveKeywordTable::new(),
            macros: HashMap::new(),
            once_included: HashSet::new(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            built_in_headers,
            lexer_stack: Vec::new(),
            pending_tokens: VecDeque::new(),
            include_depth: 0,
            max_include_depth: config.max_include_depth,
            target: config.target.clone(),
            counter: 0,
        };

        preprocessor.initialize_builtin_macros();
        preprocessor
    }

    /// Get the next value for __COUNTER__
    fn get_next_counter(&mut self) -> u32 {
        let val = self.counter;
        self.counter += 1;
        val
    }

    /// Initialize built-in macros
    fn initialize_builtin_macros(&mut self) {
        let now: DateTime<Utc> = Utc::now();

        // __DATE__
        let date_str = format!("\"{:02} {:02} {}\"", now.format("%b"), now.day(), now.year());
        let date_tokens = self.tokenize_string(&date_str);
        self.define_builtin_macro("__DATE__", date_tokens);

        // __TIME__
        let time_str = format!("\"{:02}:{:02}:{:02}\"", now.hour(), now.minute(), now.second());
        let time_tokens = self.tokenize_string(&time_str);
        self.define_builtin_macro("__TIME__", time_tokens);

        // Other built-ins
        self.define_builtin_macro(
            "__STDC__",
            vec![PPToken::new(
                PPTokenKind::Number(StringId::new("1")),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                1,
            )],
        );

        // Target specific macros
        // Architecture
        match self.target.architecture {
            Architecture::X86_64 => {
                self.define_builtin_macro_simple("__x86_64__", "1");
                self.define_builtin_macro_simple("__x86_64", "1");
                self.define_builtin_macro_simple("__amd64__", "1");
                self.define_builtin_macro_simple("__amd64", "1");
            }
            Architecture::X86_32(_) => {
                self.define_builtin_macro_simple("__i386__", "1");
                self.define_builtin_macro_simple("__i386", "1");
            }
            Architecture::Aarch64(_) => {
                self.define_builtin_macro_simple("__aarch64__", "1");
            }
            Architecture::Arm(_) => {
                self.define_builtin_macro_simple("__arm__", "1");
            }
            _ => {}
        }

        // Pointer width
        if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(64) == 64 {
            self.define_builtin_macro_simple("__LP64__", "1");
            self.define_builtin_macro_simple("_LP64", "1");
        } else {
            self.define_builtin_macro_simple("__ILP32__", "1");
            self.define_builtin_macro_simple("_ILP32", "1");
        }

        // OS
        match self.target.operating_system {
            OperatingSystem::Linux => {
                self.define_builtin_macro_simple("__linux__", "1");
                self.define_builtin_macro_simple("__linux", "1");
                self.define_builtin_macro_simple("__unix__", "1");
                self.define_builtin_macro_simple("__unix", "1");
                self.define_builtin_macro_simple("__ELF__", "1");
                self.define_builtin_macro_simple("__gnu_linux__", "1");
            }
            OperatingSystem::Darwin(_) => {
                self.define_builtin_macro_simple("__APPLE__", "1");
                self.define_builtin_macro_simple("__MACH__", "1");
            }
            OperatingSystem::Windows => {
                self.define_builtin_macro_simple("_WIN32", "1");
                if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(32) == 64 {
                    self.define_builtin_macro_simple("_WIN64", "1");
                }
            }
            _ => {}
        }

        if self.lang_opts.is_c11() {
            self.define_builtin_macro(
                "__STDC_VERSION__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("201112")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    6,
                )],
            );
            self.define_builtin_macro(
                "__STDC_HOSTED__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_MB_MIGHT_NEQ_WC__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559_COMPLEX__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_ISO_10646__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("201103L")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    7,
                )],
            );
        }

        // Variadic argument macros
        // Define va_start as function-like macro expanding to va_start
        self.define_builtin_function_macro(
            "va_start",
            vec![StringId::new("ap"), StringId::new("param")],
            vec![PPToken::new(
                PPTokenKind::Identifier(StringId::new("va_start")),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                7,
            )],
        );
        // Define va_end as function-like macro expanding to va_end
        self.define_builtin_function_macro(
            "va_end",
            vec![StringId::new("ap")],
            vec![PPToken::new(
                PPTokenKind::Identifier(StringId::new("va_end")),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                6,
            )],
        );
        // Define va_arg as function-like macro expanding to va_arg so the parser can detect it
        self.define_builtin_function_macro(
            "va_arg",
            vec![StringId::new("ap"), StringId::new("type")],
            vec![PPToken::new(
                PPTokenKind::Identifier(StringId::new("va_arg")),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                6,
            )],
        );
    }

    /// Helper to define a simple macro with a value
    fn define_builtin_macro_simple(&mut self, name: &str, value: &str) {
        let tokens = vec![PPToken::new(
            PPTokenKind::Number(StringId::new(value)),
            PPTokenFlags::empty(),
            SourceLoc::builtin(),
            value.len() as u16,
        )];
        self.define_builtin_macro(name, tokens);
    }

    /// Define a built-in macro
    fn define_builtin_macro(&mut self, name: &str, tokens: Vec<PPToken>) {
        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::builtin(),
            flags: MacroFlags::BUILTIN,
            tokens,
            parameter_list: Vec::new(),
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Define a built-in function-like macro
    fn define_builtin_function_macro(&mut self, name: &str, params: Vec<StringId>, tokens: Vec<PPToken>) {
        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::builtin(),
            flags: MacroFlags::BUILTIN | MacroFlags::FUNCTION_LIKE,
            tokens,
            parameter_list: params,
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Tokenize a string into PP tokens (simplified)
    fn tokenize_string(&self, s: &str) -> Vec<PPToken> {
        vec![PPToken::new(
            PPTokenKind::StringLiteral(StringId::new(s)),
            PPTokenFlags::empty(),
            SourceLoc::builtin(),
            s.len() as u16,
        )]
    }

    /// Check if a macro is defined
    pub(crate) fn is_macro_defined(&self, symbol: &StringId) -> bool {
        self.macros.contains_key(symbol)
    }

    /// Get the interned symbol for the "defined" operator
    pub(crate) fn defined_symbol(&self) -> StringId {
        self.directive_keywords.defined_symbol()
    }

    /// Expect and consume an Eod token or end of file
    fn expect_eod(&mut self) -> Result<(), PPError> {
        match self.lex_token() {
            Some(token) if token.kind == PPTokenKind::Eod => Ok(()),
            None => Ok(()), // End of file is acceptable
            Some(_) => Err(PPError::ExpectedEod),
        }
    }

    /// Process source file and return preprocessed tokens
    pub fn process(&mut self, source_id: SourceId, _config: &PPConfig) -> Result<Vec<PPToken>, PPError> {
        // Initialize lexer for main file
        let buffer = self.source_manager.get_buffer(source_id);
        let buffer_len = buffer.len() as u32;

        let lexer = PPLexer::new(source_id, buffer.to_vec());
        self.lexer_stack.push(lexer);

        // FIXNE: need to create line_start on the fly instead of computing all at once
        // Set line starts for the source manager so presumed locations work during processing
        let mut line_starts = vec![0];
        for (i, &byte) in buffer.iter().enumerate() {
            if byte == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        self.source_manager.set_line_starts(source_id, line_starts);

        let mut result_tokens = Vec::new();

        // Process tokens with string literal concatenation
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Hash && !token.flags.contains(PPTokenFlags::MACRO_EXPANDED) {
                // Handle directive - always process directives regardless of skipping
                self.handle_directive()?;
            } else {
                if self.is_currently_skipping() {
                    // Skip tokens when in conditional compilation skip mode
                    continue;
                }

                match token.kind {
                    PPTokenKind::Eod => continue,
                    PPTokenKind::Identifier(symbol) => {
                        let sym_str = symbol.as_str();
                        if sym_str == "__LINE__" {
                            let line = if let Some(presumed) = self.source_manager.get_presumed_location(token.location)
                            {
                                presumed.0
                            } else {
                                1
                            };
                            let line_str = line.to_string();
                            let line_symbol = StringId::new(&line_str);
                            result_tokens.push(PPToken::new(
                                PPTokenKind::Number(line_symbol),
                                PPTokenFlags::empty(),
                                token.location,
                                line_str.len() as u16,
                            ));
                        } else if sym_str == "__FILE__" {
                            let filename =
                                if let Some(presumed) = self.source_manager.get_presumed_location(token.location) {
                                    if let Some(name) = presumed.2 {
                                        format!("\"{}\"", name)
                                    } else if let Some(file_info) =
                                        self.source_manager.get_file_info(token.location.source_id())
                                    {
                                        format!("\"{}\"", file_info.path.display())
                                    } else {
                                        "\"<unknown>\"".to_string()
                                    }
                                } else if let Some(file_info) =
                                    self.source_manager.get_file_info(token.location.source_id())
                                {
                                    format!("\"{}\"", file_info.path.display())
                                } else {
                                    "\"<unknown>\"".to_string()
                                };
                            let file_symbol = StringId::new(&filename);
                            result_tokens.push(PPToken::new(
                                PPTokenKind::StringLiteral(file_symbol),
                                PPTokenFlags::empty(),
                                token.location,
                                filename.len() as u16,
                            ));
                        } else if sym_str == "__COUNTER__" {
                            let val = self.get_next_counter();
                            let val_str = val.to_string();
                            let val_symbol = StringId::new(&val_str);
                            result_tokens.push(PPToken::new(
                                PPTokenKind::Number(val_symbol),
                                PPTokenFlags::empty(),
                                token.location,
                                val_str.len() as u16,
                            ));
                        } else if sym_str == "_Pragma" {
                            self.handle_pragma_operator()?;
                        } else {
                            // Check for macro expansion
                            // Don't expand if already expanded
                            if token.flags.contains(PPTokenFlags::MACRO_EXPANDED) {
                                result_tokens.push(token);
                            } else if let Some(expanded) = self.expand_macro(&token)? {
                                // Push expanded tokens to pending_tokens (in reverse order so they come out in order)
                                for t in expanded.into_iter().rev() {
                                    self.pending_tokens.push_front(t);
                                }
                            } else {
                                result_tokens.push(token);
                            }
                        }
                    }
                    _ => {
                        result_tokens.push(token);
                    }
                }
            }
        }

        // Add EOF token
        result_tokens.push(PPToken::new(
            PPTokenKind::Eof,
            PPTokenFlags::empty(),
            SourceLoc::new(source_id, buffer_len),
            0,
        ));

        if !self.conditional_stack.is_empty() {
            let start_loc = if let Some(_info) = self.conditional_stack.last() {
                // Ideally we would have the location of the #if that started this
                // For now, use current location
                self.get_current_location()
            } else {
                self.get_current_location()
            };

            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "Unclosed preprocessor conditional directive".to_string(),
                span: SourceSpan::new(start_loc, start_loc),
                code: Some("unclosed_conditional".to_string()),
                hints: vec!["Expected #endif before end of file".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::UnexpectedEndOfFile);
        }

        Ok(result_tokens)
    }

    /// Get the current location from the lexer stack
    fn get_current_location(&self) -> SourceLoc {
        if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
        } else {
            SourceLoc::builtin()
        }
    }

    /// Check if we are currently skipping tokens
    fn is_currently_skipping(&self) -> bool {
        // Check if any conditional in the stack is currently skipping
        self.conditional_stack.iter().any(|info| info.was_skipping)
    }

    /// Set the skipping state for the current conditional level
    fn set_skipping(&mut self, skipping: bool) {
        if let Some(info) = self.conditional_stack.last_mut() {
            info.was_skipping = skipping;
        } else {
            // No conditionals, don't skip
        }
    }

    /// Parse a conditional expression for #if and #elif
    fn parse_conditional_expression(&mut self) -> Result<Vec<PPToken>, PPError> {
        let mut tokens = Vec::new();
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        while let Some(token) = self.lex_token() {
            let token_line = if let Some(lexer) = self.lexer_stack.last() {
                lexer.get_line(token.location.offset())
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
            let span = SourceSpan::new(self.get_current_location(), self.get_current_location());
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "Invalid conditional expression".to_string(),
                span,
                code: Some("invalid_conditional_expression".to_string()),
                hints: vec!["Conditional directives require an expression".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::InvalidConditionalExpression);
        }

        Ok(tokens)
    }

    /// Evaluate a conditional expression (simplified - handle defined and basic arithmetic)
    fn evaluate_conditional_expression(&mut self, tokens: &[PPToken]) -> Result<bool, PPError> {
        // Filter out Eod tokens
        let tokens: Vec<PPToken> = tokens.iter().filter(|t| t.kind != PPTokenKind::Eod).cloned().collect();

        if tokens.is_empty() {
            // For empty expressions, treat as false
            return Ok(false);
        }

        // Check for defined(identifier) or defined identifier before macro expansion
        if tokens.len() >= 2 && matches!(tokens[0].kind, PPTokenKind::Identifier(sym) if sym == self.defined_symbol()) {
            if tokens.len() == 2 {
                // defined identifier
                if let PPTokenKind::Identifier(sym) = &tokens[1].kind {
                    let is_defined = self.macros.contains_key(sym);
                    return Ok(is_defined);
                }
            } else if tokens.len() >= 4
                && matches!(tokens[1].kind, PPTokenKind::LeftParen)
                && matches!(tokens[3].kind, PPTokenKind::RightParen)
            {
                // defined(identifier)
                if let PPTokenKind::Identifier(sym) = &tokens[2].kind {
                    let is_defined = self.macros.contains_key(sym);
                    return Ok(is_defined);
                }
            }
        }

        // First, expand macros in the expression
        let mut expanded_tokens = tokens.to_vec();
        match self.expand_tokens(&mut expanded_tokens) {
            Ok(_) => {}
            Err(_e) => {
                // If macro expansion fails, emit diagnostic and treat as false
                let span = if !tokens.is_empty() {
                    SourceSpan::new(tokens[0].location, tokens.last().unwrap().location)
                } else {
                    let loc = self.get_current_location();
                    SourceSpan::new(loc, loc)
                };
                let diag = Diagnostic {
                    level: DiagnosticLevel::Warning,
                    message: "Failed to expand macros in conditional expression".to_string(),
                    span,
                    code: Some("macro_expansion_failed".to_string()),
                    hints: vec!["Expression will be treated as false".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Ok(false);
            }
        }

        // Evaluate arithmetic expression with better error handling
        self.evaluate_arithmetic_expression(&expanded_tokens)
    }

    /// Evaluate a simple arithmetic expression for #if/#elif
    fn evaluate_arithmetic_expression(&mut self, tokens: &[PPToken]) -> Result<bool, PPError> {
        if tokens.is_empty() {
            return Err(PPError::InvalidConditionalExpression);
        }

        let mut interpreter = Interpreter::new(tokens, self);
        let result = interpreter.evaluate();

        match result {
            Ok(val) => Ok(val != 0),
            Err(_) => {
                // For complex expressions that can't be parsed, emit a warning and treat as false
                let span = if !tokens.is_empty() {
                    SourceSpan::new(tokens[0].location, tokens.last().unwrap().location)
                } else {
                    let loc = self.get_current_location();
                    SourceSpan::new(loc, loc)
                };
                let diag = Diagnostic {
                    level: DiagnosticLevel::Warning,
                    message: "Invalid conditional expression in preprocessor directive".to_string(),
                    span,
                    code: Some("invalid_conditional_expression".to_string()),
                    hints: vec!["Expression will be treated as false".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                // Return false for unparseable expressions to allow compilation to continue
                Ok(false)
            }
        }
    }

    /// Lex the next token
    fn lex_token(&mut self) -> Option<PPToken> {
        if let Some(token) = self.pending_tokens.pop_front() {
            return Some(token);
        }

        loop {
            if let Some(lexer) = self.lexer_stack.last_mut() {
                if let Some(token) = lexer.next_token() {
                    return Some(token);
                } else {
                    // EOF reached, pop the lexer
                    let popped_lexer = self.lexer_stack.pop().unwrap();

                    // If this was an included file, pop from include stack and decrement depth.
                    if let Some(include_info) = self.include_stack.last()
                        && include_info.file_id == popped_lexer.source_id
                    {
                        self.include_stack.pop();
                        self.include_depth -= 1;
                    }

                    // Set the line_starts from the lexer to the source manager
                    self.source_manager
                        .set_line_starts(popped_lexer.source_id, popped_lexer.get_line_starts().clone());
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
    fn handle_directive(&mut self) -> Result<(), PPError> {
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;

        match token.kind {
            PPTokenKind::Identifier(sym) => {
                // Use O(1) interned keyword comparison
                match self.directive_keywords.is_directive(sym) {
                    Some(DirectiveKind::Define) => self.check_skipping_and_execute(|this| this.handle_define()),
                    Some(DirectiveKind::Undef) => self.check_skipping_and_execute(|this| this.handle_undef()),
                    Some(DirectiveKind::Include) => self.check_skipping_and_execute(|this| this.handle_include()),
                    Some(DirectiveKind::If) => {
                        // Always process #if to track nesting
                        if self.is_currently_skipping() {
                            self.push_skipped_conditional();
                            self.skip_directive()?;
                        } else {
                            let expr_tokens = self.parse_conditional_expression().unwrap_or_default();
                            let condition = self.evaluate_conditional_expression(&expr_tokens).unwrap_or(false);
                            self.handle_if_directive(condition)?;
                        }
                        Ok(())
                    }
                    Some(DirectiveKind::Ifdef) => {
                        if self.is_currently_skipping() {
                            self.push_skipped_conditional();
                            self.skip_directive()?;
                        } else {
                            self.handle_ifdef()?;
                        }
                        Ok(())
                    }
                    Some(DirectiveKind::Ifndef) => {
                        if self.is_currently_skipping() {
                            self.push_skipped_conditional();
                            self.skip_directive()?;
                        } else {
                            self.handle_ifndef()?;
                        }
                        Ok(())
                    }
                    Some(DirectiveKind::Elif) => {
                        if self.should_evaluate_conditional() {
                            let expr_tokens = self.parse_conditional_expression().unwrap_or_default();
                            let condition = self.evaluate_conditional_expression(&expr_tokens).unwrap_or(false);
                            self.handle_elif_directive(condition, token.location)?;
                        } else {
                            // Just update state to keep skipping
                            self.handle_elif_directive(false, token.location)?;
                        }
                        Ok(())
                    }
                    Some(DirectiveKind::Else) => self.handle_else(token.location),
                    Some(DirectiveKind::Endif) => self.handle_endif(token.location),
                    Some(DirectiveKind::Line) => self.check_skipping_and_execute(|this| this.handle_line()),
                    Some(DirectiveKind::Pragma) => self.check_skipping_and_execute(|this| this.handle_pragma()),
                    Some(DirectiveKind::Error) => self.check_skipping_and_execute(|this| this.handle_error()),
                    Some(DirectiveKind::Warning) => self.check_skipping_and_execute(|this| this.handle_warning()),
                    None => {
                        let name = sym.as_str();
                        let diag = Diagnostic {
                            level: DiagnosticLevel::Error,
                            message: format!("Invalid preprocessor directive '{name}'"),
                            span: SourceSpan::new(token.location, token.location),
                            code: Some("invalid_directive".to_string()),
                            hints: vec!["Valid directives include #define, #include, #if, #ifdef, #ifndef, #elif, #else, #endif, #line, #pragma, #error, #warning".to_string()],
                            related: Vec::new(),
                        };
                        self.diag.report_diagnostic(diag);
                        Err(PPError::InvalidDirective)
                    }
                }
            }
            _ => {
                let diag = Diagnostic {
                    level: DiagnosticLevel::Error,
                    message: "Invalid preprocessor directive".to_string(),
                    span: SourceSpan::new(token.location, token.location),
                    code: Some("invalid_directive".to_string()),
                    hints: vec!["Valid directives include #define, #include, #if, #ifdef, #ifndef, #elif, #else, #endif, #line, #pragma, #error, #warning".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                Err(PPError::InvalidDirective)
            }
        }
    }

    /// Check if skipping is active, and if so, skip the directive. Otherwise, execute the action.
    fn check_skipping_and_execute<F>(&mut self, action: F) -> Result<(), PPError>
    where
        F: FnOnce(&mut Self) -> Result<(), PPError>,
    {
        if self.is_currently_skipping() {
            self.skip_directive()
        } else {
            action(self)
        }
    }

    /// Handle _Pragma("...") operator
    fn handle_pragma_operator(&mut self) -> Result<(), PPError> {
        // We have already consumed the `_Pragma` identifier.
        // Expect '('.
        if self.lex_token().is_none_or(|t| t.kind != PPTokenKind::LeftParen) {
            return Err(PPError::InvalidDirective);
        }

        // Expect string literal.
        let string_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let pragma_content = if let PPTokenKind::StringLiteral(symbol) = string_token.kind {
            self.destringize(symbol.as_str())
        } else {
            return Err(PPError::InvalidDirective);
        };

        // Expect ')'.
        if self.lex_token().is_none_or(|t| t.kind != PPTokenKind::RightParen) {
            return Err(PPError::InvalidDirective);
        }

        self.perform_pragma(&pragma_content);

        Ok(())
    }

    /// Destringize a string literal (remove quotes and handle escapes)
    fn destringize(&self, full_str: &str) -> String {
        let inner_content = &full_str[1..full_str.len() - 1];
        let mut content = String::with_capacity(inner_content.len());
        let mut chars = inner_content.chars();
        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('"') => content.push('"'),
                    Some('\\') => content.push('\\'),
                    Some(other) => {
                        content.push('\\');
                        content.push(other);
                    }
                    None => {} // Invalid escape at end of string
                }
            } else {
                content.push(c);
            }
        }
        content
    }

    /// Perform the action of a pragma directive
    fn perform_pragma(&mut self, pragma_content: &str) {
        // Get the source_id of the file containing the _Pragma operator for context.
        let pragma_source_id = self.lexer_stack.last().map(|l| l.source_id);

        // --- Process the pragma content without modifying the main lexer stack ---
        let source_id = self
            .source_manager
            .add_buffer(pragma_content.as_bytes().to_vec(), "<_Pragma>", None);
        let buffer = self.source_manager.get_buffer(source_id);
        let mut temp_lexer = PPLexer::new(source_id, buffer.to_vec());

        // Process all tokens from the pragma's content.
        while let Some(pragma_token) = temp_lexer.next_token() {
            if let PPTokenKind::Identifier(symbol) = pragma_token.kind
                && symbol.as_str() == "once"
            {
                if let Some(id) = pragma_source_id {
                    self.once_included.insert(id);
                }
                // After "once", no other tokens matter.
                break;
            }
            // Other pragma directives are tokenized but currently ignored.
        }
    }

    /// Handle #define directive
    fn handle_define(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };

        let mut flags = MacroFlags::empty();
        let mut params = Vec::new();
        let mut variadic = None;
        let next = self.lex_token();
        if let Some(token) = next {
            if token.kind == PPTokenKind::LeftParen {
                let first_param = self.lex_token();
                if let Some(fp) = first_param {
                    if matches!(
                        fp.kind,
                        PPTokenKind::RightParen | PPTokenKind::Identifier(_) | PPTokenKind::Ellipsis
                    ) {
                        flags |= MacroFlags::FUNCTION_LIKE;
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(fp);
                        }
                        // parse params
                        'param_parsing: loop {
                            let param_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                            match param_token.kind {
                                PPTokenKind::RightParen => break,
                                PPTokenKind::Identifier(sym) => {
                                    if params.contains(&sym) {
                                        return Err(PPError::InvalidMacroParameter {
                                            span: SourceSpan::new(
                                                self.get_current_location(),
                                                self.get_current_location(),
                                            ),
                                        });
                                    }
                                    params.push(sym);
                                    let sep = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                                    match sep.kind {
                                        PPTokenKind::Comma => continue,
                                        PPTokenKind::RightParen => break,
                                        PPTokenKind::Ellipsis => {
                                            variadic = Some(sym);
                                            flags |= MacroFlags::C99_VARARGS;
                                            let rparen = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                                            if rparen.kind != PPTokenKind::RightParen {
                                                return Err(PPError::InvalidMacroParameter {
                                                    span: SourceSpan::new(
                                                        self.get_current_location(),
                                                        self.get_current_location(),
                                                    ),
                                                });
                                            }
                                            break;
                                        }
                                        _ => {
                                            // Check if this token could signal the end of parameter list
                                            // For object-like macros, any non-identifier token after the macro name
                                            // should be treated as the start of the macro body
                                            if let Some(lexer) = self.lexer_stack.last_mut() {
                                                lexer.put_back(param_token);
                                            }
                                            // This is an object-like macro, exit parameter parsing
                                            break 'param_parsing;
                                        }
                                    }
                                }
                                PPTokenKind::Ellipsis => {
                                    flags |= MacroFlags::GNU_VARARGS;
                                    variadic = Some(StringId::new("__VA_ARGS__"));
                                    let rparen = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                                    if rparen.kind != PPTokenKind::RightParen {
                                        return Err(PPError::InvalidMacroParameter {
                                            span: SourceSpan::new(
                                                self.get_current_location(),
                                                self.get_current_location(),
                                            ),
                                        });
                                    }
                                    break;
                                }
                                _ => {
                                    // For problematic parameter tokens, emit a warning and continue
                                    let diag = Diagnostic {
                                        level: DiagnosticLevel::Warning,
                                        message: format!(
                                            "Invalid macro parameter token in #define '{}'",
                                            name.as_str()
                                        ),
                                        span: SourceSpan::new(param_token.location, param_token.location),
                                        code: Some("invalid_macro_parameter".to_string()),
                                        hints: vec!["Macro parameters must be identifiers".to_string()],
                                        related: Vec::new(),
                                    };
                                    self.diag.report_diagnostic(diag);

                                    // Skip to the next comma or right paren
                                    loop {
                                        let skip_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                                        match skip_token.kind {
                                            PPTokenKind::Comma | PPTokenKind::RightParen => {
                                                if let Some(lexer) = self.lexer_stack.last_mut() {
                                                    lexer.put_back(skip_token);
                                                }
                                                break;
                                            }
                                            _ => continue,
                                        }
                                    }
                                }
                            }
                        }
                    } else if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(fp);
                        lexer.put_back(token);
                    }
                } else {
                    return Err(PPError::UnexpectedEndOfFile);
                }
            } else if let Some(lexer) = self.lexer_stack.last_mut() {
                lexer.put_back(token);
            }
        }
        let mut tokens = Vec::new();
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
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

        // Check for macro redefinition
        if let Some(existing) = self.macros.get(&name) {
            let is_builtin = existing.flags.contains(MacroFlags::BUILTIN);

            // Check if definition is different
            // Two macro definitions are distinct if they have different parameter lists,
            // different variadic arguments, different flags, or different token sequences.
            // For token sequences, we check kind and flags (ignoring location).
            let is_different = existing.flags != macro_info.flags
                || existing.parameter_list != macro_info.parameter_list
                || existing.variadic_arg != macro_info.variadic_arg
                || existing.tokens.len() != macro_info.tokens.len()
                || existing
                    .tokens
                    .iter()
                    .zip(macro_info.tokens.iter())
                    .any(|(a, b)| a.kind != b.kind || a.flags != b.flags);

            if !is_builtin && is_different {
                // Emit warning for redefinition
                let diag = Diagnostic {
                    level: DiagnosticLevel::Warning,
                    message: format!("Redefinition of macro '{}'", name.as_str()),
                    span: SourceSpan::new(name_token.location, name_token.location),
                    code: Some("macro_redefinition".to_string()),
                    hints: Vec::new(),
                    related: vec![SourceSpan::new(existing.location, existing.location)],
                };
                self.diag.report_diagnostic(diag);
            }
        }

        self.macros.insert(name, macro_info);
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };
        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn handle_include(&mut self) -> Result<(), PPError> {
        // Parse the include path
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let is_angled = matches!(token.kind, PPTokenKind::Less);
        let path_str = match token.kind {
            PPTokenKind::StringLiteral(symbol) => {
                // Remove quotes from string literal
                let full_str = symbol.as_str();
                if full_str.starts_with('"') && full_str.ends_with('"') {
                    full_str[1..full_str.len() - 1].to_string()
                } else {
                    return Err(PPError::InvalidIncludePath);
                }
            }
            PPTokenKind::Less => {
                // Angled include: collect tokens until >
                let mut path_parts = Vec::new();
                loop {
                    let part_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                    match part_token.kind {
                        PPTokenKind::Greater => break,
                        _ => path_parts.push(part_token),
                    }
                }
                // Concatenate the path parts
                let mut path = String::new();
                for part in path_parts.iter() {
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
            _ => return Err(PPError::InvalidIncludePath),
        };

        // Check include depth
        if self.include_depth >= self.max_include_depth {
            // Arbitrary limit
            return Err(PPError::IncludeDepthExceeded);
        }

        // Check for built-in headers first for angled includes
        let include_source_id = if is_angled {
            if let Some(content) = self.built_in_headers.get(path_str.as_str()) {
                self.source_manager
                    .add_buffer(content.as_bytes().to_vec(), &path_str, Some(token.location))
            } else {
                // Get current directory
                let current_file_id = self.lexer_stack.last().unwrap().source_id;
                let current_file_info = self.source_manager.get_file_info(current_file_id).unwrap();
                let current_dir = current_file_info.path.parent().unwrap_or(Path::new("."));

                // Resolve the path
                let resolved_path = self.header_search.resolve_path(&path_str, is_angled, current_dir);
                if let Some(resolved_path) = resolved_path {
                    // Load the file
                    self.source_manager
                        .add_file_from_path(&resolved_path, Some(token.location))
                        .map_err(|_| {
                            // Emit diagnostic for file not found
                            let diag = Diagnostic {
                                level: DiagnosticLevel::Error,
                                message: format!("Include file '{}' not found", path_str),
                                span: SourceSpan::new(token.location, token.location),
                                code: Some("include_file_not_found".to_string()),
                                hints: vec!["Check the include path and ensure the file exists".to_string()],
                                related: Vec::new(),
                            };
                            self.diag.report_diagnostic(diag);
                            PPError::FileNotFound
                        })?
                } else {
                    // Emit diagnostic for file not found
                    let diag = Diagnostic {
                        level: DiagnosticLevel::Error,
                        message: format!("Include file '{}' not found", path_str),
                        span: SourceSpan::new(token.location, token.location),
                        code: Some("include_file_not_found".to_string()),
                        hints: vec!["Check the include path and ensure the file exists".to_string()],
                        related: Vec::new(),
                    };
                    self.diag.report_diagnostic(diag);
                    return Err(PPError::FileNotFound);
                }
            }
        } else {
            // For quoted includes, resolve as before
            let resolved_path = if is_angled {
                self.header_search.resolve_path(&path_str, true, Path::new("."))
            } else {
                let current_file_id = self.lexer_stack.last().unwrap().source_id;
                let current_file_info = self.source_manager.get_file_info(current_file_id).unwrap();
                let current_dir = current_file_info.path.parent().unwrap_or(Path::new("."));
                self.header_search.resolve_path(&path_str, false, current_dir)
            };

            if let Some(resolved_path) = resolved_path {
                self.source_manager
                    .add_file_from_path(&resolved_path, Some(token.location))
                    .map_err(|_| {
                        // Emit diagnostic for file not found
                        let diag = Diagnostic {
                            level: DiagnosticLevel::Error,
                            message: format!("Include file '{}' not found", path_str),
                            span: SourceSpan::new(token.location, token.location),
                            code: Some("include_file_not_found".to_string()),
                            hints: vec!["Check the include path and ensure the file exists".to_string()],
                            related: Vec::new(),
                        };
                        self.diag.report_diagnostic(diag);
                        PPError::FileNotFound
                    })?
            } else if let Some(file_id) = self.source_manager.get_file_id(&path_str) {
                file_id
            } else {
                // Emit diagnostic for file not found
                let diag = Diagnostic {
                    level: DiagnosticLevel::Error,
                    message: format!("Include file '{}' not found", path_str),
                    span: SourceSpan::new(token.location, token.location),
                    code: Some("include_file_not_found".to_string()),
                    hints: vec!["Check the include path and ensure the file exists".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Err(PPError::FileNotFound);
            }
        };

        // Check if file has #pragma once
        if self.once_included.contains(&include_source_id) {
            // Skip including this file again
            return Ok(());
        }

        // Push to include stack
        self.include_stack.push(IncludeStackInfo {
            file_id: include_source_id,
            // location: token.location,
        });

        self.expect_eod()?;

        // Create lexer for the included file
        let buffer = self.source_manager.get_buffer(include_source_id);
        let lexer = PPLexer::new(include_source_id, buffer.to_vec());
        self.lexer_stack.push(lexer);

        self.include_depth += 1;

        Ok(())
    }
    fn handle_if_directive(&mut self, condition: bool) -> Result<(), PPError> {
        // Push new conditional state
        let info = PPConditionalInfo {
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: condition, // Set to true if condition is true
        };
        self.conditional_stack.push(info);

        // Set skipping state for this conditional level
        if !condition {
            self.set_skipping(true);
        }

        Ok(())
    }

    fn handle_ifdef(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };

        let defined = self.macros.contains_key(&name);
        let info = PPConditionalInfo {
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: defined,
        };
        self.conditional_stack.push(info);

        // Set skipping state for this conditional level
        if !defined {
            self.set_skipping(true);
        }

        self.expect_eod()?;

        Ok(())
    }

    fn handle_ifndef(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };

        let defined = self.macros.contains_key(&name);
        let info = PPConditionalInfo {
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: !defined,
        };
        self.conditional_stack.push(info);

        // Set skipping state for this conditional level
        if defined {
            self.set_skipping(true);
        }

        self.expect_eod()?;

        Ok(())
    }

    fn handle_elif_directive(&mut self, condition: bool, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "#elif without #if".to_string(),
                span: SourceSpan::new(location, location),
                code: Some("elif_without_if".to_string()),
                hints: vec!["#elif must be preceded by #if, #ifdef, or #ifndef".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::ElifWithoutIf);
        }

        let current = self.conditional_stack.last_mut().unwrap();
        if current.found_else {
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "#elif after #else".to_string(),
                span: SourceSpan::new(location, location),
                code: Some("elif_after_else".to_string()),
                hints: vec!["#else must be the last directive in a conditional block".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::UnmatchedElif);
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

    fn handle_else(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "#else without #if".to_string(),
                span: SourceSpan::new(location, location),
                code: Some("else_without_if".to_string()),
                hints: vec!["#else must be preceded by #if, #ifdef, or #ifndef".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::ElseWithoutIf);
        }

        let current = self.conditional_stack.last_mut().unwrap();
        if current.found_else {
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "Multiple #else directives".to_string(),
                span: SourceSpan::new(location, location),
                code: Some("multiple_else".to_string()),
                hints: vec!["A conditional block can only have one #else".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::UnmatchedElse);
        }
        current.found_else = true;

        // Process else block if no previous branch was taken
        let should_process = !current.found_non_skipping;

        // Only change the skipping state for the current conditional level
        current.was_skipping = !should_process;

        self.expect_eod()?;

        Ok(())
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            let diag = Diagnostic {
                level: DiagnosticLevel::Error,
                message: "Unmatched #endif".to_string(),
                span: SourceSpan::new(location, location),
                code: Some("unmatched_endif".to_string()),
                hints: vec!["#endif must be preceded by #if, #ifdef, or #ifndef".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PPError::UnmatchedEndif);
        }

        let _info = self.conditional_stack.pop().unwrap();
        // Restore previous skipping state - checking the stack implicitly restores it

        self.expect_eod()?;

        Ok(())
    }
    fn handle_line(&mut self) -> Result<(), PPError> {
        // Collect tokens until end of line
        let mut tokens = Vec::new();
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }

        if tokens.is_empty() {
            return Err(PPError::InvalidLineDirective);
        }

        // Expand macros in tokens
        self.expand_tokens(&mut tokens)?;

        if tokens.is_empty() {
            return Err(PPError::InvalidLineDirective);
        }

        // Parse line number
        let logical_line = match &tokens[0].kind {
            PPTokenKind::Number(symbol) => {
                let text = symbol.as_str();
                text.parse::<u32>().map_err(|_| PPError::InvalidLineDirective)?
            }
            _ => return Err(PPError::InvalidLineDirective),
        };

        // Validate line number (should be positive)
        if logical_line == 0 {
            return Err(PPError::InvalidLineDirective);
        }

        // Optional filename
        let logical_file = if tokens.len() > 1 {
            match &tokens[1].kind {
                PPTokenKind::StringLiteral(symbol) => {
                    let full_str = symbol.as_str();
                    if full_str.starts_with('"') && full_str.ends_with('"') {
                        Some(full_str[1..full_str.len() - 1].to_string())
                    } else {
                        return Err(PPError::InvalidLineDirective);
                    }
                }
                _ => return Err(PPError::InvalidLineDirective), // Extra tokens that aren't filename
            }
        } else {
            None
        };

        // Check for too many tokens
        if tokens.len() > 2 {
            return Err(PPError::InvalidLineDirective);
        }

        // Get current physical line (where #line directive appears)
        let physical_line = start_line;

        // The #line directive sets the line number for the following line,
        // so we need to adjust the logical_line for the entry
        let entry_logical_line = logical_line - 1;

        // Add entry to LineMap
        if let Some(lexer) = self.lexer_stack.last()
            && let Some(line_map) = self.source_manager.get_line_map_mut(lexer.source_id)
        {
            let entry = crate::source_manager::LineDirective::new(physical_line, entry_logical_line, logical_file);
            line_map.add_entry(entry);
        }

        Ok(())
    }
    fn handle_pragma(&mut self) -> Result<(), PPError> {
        // Parse the pragma directive
        let pragma_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        match pragma_token.kind {
            PPTokenKind::Identifier(symbol) => {
                let pragma_name = symbol.as_str();
                if pragma_name == "once" {
                    // Mark the current file as once-included
                    if let Some(lexer) = self.lexer_stack.last() {
                        self.once_included.insert(lexer.source_id);
                    }
                } else {
                    let diag = Diagnostic {
                        level: DiagnosticLevel::Error,
                        message: format!("Unknown pragma '{}'", pragma_name),
                        span: SourceSpan::new(pragma_token.location, pragma_token.location),
                        code: Some("unknown_pragma".to_string()),
                        hints: vec!["Only '#pragma once' is supported".to_string()],
                        related: Vec::new(),
                    };
                    self.diag.report_diagnostic(diag);
                    return Err(PPError::UnknownPragma(pragma_name.to_string()));
                }
            }
            _ => {
                let diag = Diagnostic {
                    level: DiagnosticLevel::Error,
                    message: "Invalid pragma directive".to_string(),
                    span: SourceSpan::new(pragma_token.location, pragma_token.location),
                    code: Some("invalid_pragma".to_string()),
                    hints: vec!["Pragma directive requires an identifier".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Err(PPError::InvalidDirective);
            }
        }
        // Skip to end of line
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
        }
        Ok(())
    }

    fn handle_error(&mut self) -> Result<(), PPError> {
        // Note: Skipping is handled by caller (check_skipping_and_execute)

        let directive_location = self.get_current_location();
        let message = self.consume_rest_of_line_as_string();

        let diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message: format!("#error directive: {}", message),
            span: SourceSpan::new(directive_location, directive_location),
            ..Default::default()
        };
        self.diag.report_diagnostic(diag);
        Err(PPError::ErrorDirective(message))
    }

    fn handle_warning(&mut self) -> Result<(), PPError> {
        // Note: Skipping is handled by caller (check_skipping_and_execute)

        let directive_location = self.get_current_location();
        let message = self.consume_rest_of_line_as_string();

        // For warning, we emit a diagnostic but don't stop compilation
        let diag = Diagnostic {
            level: DiagnosticLevel::Warning,
            message,
            span: SourceSpan::new(directive_location, directive_location),
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diag.report_diagnostic(diag);
        Ok(())
    }

    fn consume_rest_of_line_as_string(&mut self) -> String {
        let mut message_parts = Vec::new();
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
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
        message_parts.join(" ")
    }

    /// Expand a macro if it exists
    fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPError> {
        if let PPTokenKind::Identifier(symbol) = token.kind {
            // Check if macro exists and is not disabled
            let macro_info = match self.macros.get(&symbol) {
                Some(m) if !m.flags.contains(MacroFlags::DISABLED) => m.clone(),
                _ => return Ok(None),
            };

            // For function-like macros, check if followed by '('
            if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
                let next = self.lex_token();
                match next {
                    Some(t) if t.kind == PPTokenKind::LeftParen => {
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(t);
                        }
                    }
                    Some(t) => {
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(t);
                        }
                        return Ok(None);
                    }
                    None => return Ok(None),
                }
            }

            // Check for recursion
            if macro_info.flags.contains(MacroFlags::DISABLED) {
                return Err(PPError::MacroRecursion);
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
                self.expand_function_macro(&macro_info, &symbol, token)
            } else {
                self.expand_object_macro(&macro_info, &symbol, token)
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

    /// Helper to convert tokens to their string representation
    fn tokens_to_string(&self, tokens: &[PPToken]) -> String {
        let mut result = String::new();
        for token in tokens {
            result.push_str(token.get_text());
        }
        result
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        // For Level B: Create a virtual buffer containing the replacement text
        let replacement_text = self.tokens_to_string(&macro_info.tokens);
        let virtual_buffer = replacement_text.into_bytes();
        let virtual_id = self.source_manager.add_virtual_buffer(
            virtual_buffer,
            &format!("macro_{}", symbol.as_str()),
            Some(token.location),
        );

        // Create tokens with locations in the virtual buffer
        let mut expanded = Vec::new();
        let mut offset = 0u32;

        for original_token in &macro_info.tokens {
            let token_text = original_token.get_text();
            let token_len = token_text.len() as u16;

            let new_token = PPToken::new(
                original_token.kind,
                original_token.flags | PPTokenFlags::MACRO_EXPANDED,
                SourceLoc::new(virtual_id, offset),
                token_len,
            );

            expanded.push(new_token);
            offset += token_len as u32;
        }

        // Recursively expand any macros in the replacement
        self.expand_tokens(&mut expanded)?;

        Ok(expanded)
    }

    /// Expand a function-like macro
    fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        // Parse arguments from lexer
        let args = self.parse_macro_args_from_lexer(macro_info)?;

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            self.expand_tokens(&mut arg_clone)?;
            expanded_args.push(arg_clone);
        }

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args, &expanded_args)?;

        // For Level B: Create a virtual buffer containing the substituted text
        let replacement_text = self.tokens_to_string(&substituted);
        let virtual_buffer = replacement_text.into_bytes();
        let virtual_id = self.source_manager.add_virtual_buffer(
            virtual_buffer,
            &format!("macro_{}", symbol.as_str()),
            Some(token.location),
        );

        // Create tokens with locations in the virtual buffer
        let mut expanded = Vec::new();
        let mut offset = 0u32;

        for original_token in &substituted {
            let token_text = original_token.get_text();
            let token_len = token_text.len() as u16;

            let new_token = PPToken::new(
                original_token.kind,
                original_token.flags | PPTokenFlags::MACRO_EXPANDED,
                SourceLoc::new(virtual_id, offset),
                token_len,
            );

            expanded.push(new_token);
            offset += token_len as u32;
        }

        // Recursively expand any macros in the replacement
        self.expand_tokens(&mut expanded)?;

        Ok(expanded)
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(&mut self, macro_info: &MacroInfo) -> Result<Vec<Vec<PPToken>>, PPError> {
        // Skip whitespace and expect '('
        let mut found_lparen = false;
        while let Some(token) = self.lex_token() {
            match token.kind {
                PPTokenKind::LeftParen => {
                    found_lparen = true;
                    break;
                }
                PPTokenKind::Eof => return Err(PPError::UnexpectedEndOfFile),
                _ if token.flags.contains(PPTokenFlags::LEADING_SPACE) => continue,
                _ => {
                    // Put back non-whitespace token
                    if let Some(lexer) = self.lexer_stack.last_mut() {
                        lexer.put_back(token);
                    }
                    return Err(PPError::InvalidMacroParameter {
                        span: SourceSpan::new(token.location, token.location),
                    });
                }
            }
        }

        if !found_lparen {
            return Err(PPError::UnexpectedEndOfFile);
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
                PPTokenKind::Comma if paren_depth == 0 && brace_depth == 0 && bracket_depth == 0 => {
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
                return Err(PPError::InvalidMacroParameter {
                    span: SourceSpan::new(macro_info.location, macro_info.location),
                });
            }
        } else if args.len() != expected_args {
            return Err(PPError::InvalidMacroParameter {
                span: SourceSpan::new(macro_info.location, macro_info.location),
            });
        }

        Ok(args)
    }

    /// Substitute parameters in macro body
    fn substitute_macro(
        &mut self,
        macro_info: &MacroInfo,
        args: &[Vec<PPToken>],
        expanded_args: &[Vec<PPToken>],
    ) -> Result<Vec<PPToken>, PPError> {
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
                            if let Some(param_index) = macro_info.parameter_list.iter().position(|&p| p == param_symbol)
                            {
                                // Argument is used with #, so use unexpanded tokens
                                let arg_tokens = &args[param_index];
                                let stringified = self.stringify_tokens(arg_tokens, token.location)?;
                                result.push(stringified);
                                i += 2;
                                continue;
                            } else if macro_info.variadic_arg == Some(param_symbol) {
                                // Handle variadic argument
                                let start_index = macro_info.parameter_list.len();
                                let variadic_args =
                                    args.iter().skip(start_index).flatten().cloned().collect::<Vec<_>>();
                                let stringified = self.stringify_tokens(&variadic_args, token.location)?;
                                result.push(stringified);
                                i += 2;
                                continue;
                            }
                        }
                    }
                    result.push(*token);
                }
                PPTokenKind::HashHash => {
                    // Token pasting operator
                    if i + 1 < macro_info.tokens.len() {
                        let right_token = &macro_info.tokens[i + 1];

                        // Determine the left operand for pasting
                        let left_tokens = if !result.is_empty() {
                            vec![result.pop().unwrap()]
                        } else {
                            Vec::new()
                        };

                        // Determine the right operand for pasting
                        let right_tokens = if let PPTokenKind::Identifier(symbol) = right_token.kind {
                            if let Some(param_index) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
                                // Argument is preceded by ##, so use unexpanded tokens
                                args[param_index].clone()
                            } else if macro_info.variadic_arg == Some(symbol) {
                                let start_index = macro_info.parameter_list.len();
                                args.iter().skip(start_index).flatten().cloned().collect()
                            } else {
                                vec![*right_token]
                            }
                        } else {
                            vec![*right_token]
                        };

                        // If either side is empty, the ## operator has no effect on that side
                        if left_tokens.is_empty() && !right_tokens.is_empty() {
                            result.extend(right_tokens);
                        } else if !left_tokens.is_empty() && right_tokens.is_empty() {
                            result.extend(left_tokens);
                        } else if !left_tokens.is_empty() && !right_tokens.is_empty() {
                            // Both sides have tokens, perform the paste
                            let pasted = self.paste_tokens(&left_tokens[0], &right_tokens[0])?;
                            result.extend(pasted);
                            // If there are more tokens on the right side, append them
                            if right_tokens.len() > 1 {
                                result.extend_from_slice(&right_tokens[1..]);
                            }
                        }

                        i += 2; // Consume ## and the right-hand token
                        continue;
                    }
                    // If ## is at the end of the macro, just push it (though this is invalid)
                    result.push(*token);
                }
                PPTokenKind::Identifier(symbol) => {
                    // Parameter substitution
                    if let Some(param_index) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
                        // Check if followed by ##
                        let next_is_hashhash = if i + 1 < macro_info.tokens.len() {
                            macro_info.tokens[i + 1].kind == PPTokenKind::HashHash
                        } else {
                            false
                        };

                        if next_is_hashhash {
                            // Argument is followed by ##, use unexpanded tokens
                            result.extend(args[param_index].clone());
                        } else {
                            // Argument is not involved in # or ## (preceding check handled by ## logic), use expanded tokens
                            result.extend(expanded_args[param_index].clone());
                        }
                    } else if macro_info.variadic_arg == Some(symbol) {
                        // Handle variadic argument
                        let start_index = macro_info.parameter_list.len();

                        // Check if followed by ##
                        let next_is_hashhash = if i + 1 < macro_info.tokens.len() {
                            macro_info.tokens[i + 1].kind == PPTokenKind::HashHash
                        } else {
                            false
                        };

                        // Decide which args to use (unexpanded or expanded)
                        // Note: For variadic, we need to collect slices of args
                        let source_args = if next_is_hashhash { args } else { expanded_args };

                        let mut first = true;
                        for arg in source_args.iter().skip(start_index) {
                            if !first {
                                result.push(PPToken::new(
                                    PPTokenKind::Comma,
                                    PPTokenFlags::empty(),
                                    token.location,
                                    1,
                                ));
                            }
                            result.extend(arg.clone());
                            first = false;
                        }
                    } else {
                        result.push(*token);
                    }
                }
                _ => {
                    result.push(*token);
                }
            }
            i += 1;
        }

        Ok(result)
    }

    /// Stringify tokens for # operator
    fn stringify_tokens(&self, tokens: &[PPToken], location: SourceLoc) -> Result<PPToken, PPError> {
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
                return Err(PPError::InvalidStringification);
            }
        }

        result.push('"');

        Ok(PPToken::new(
            PPTokenKind::StringLiteral(StringId::new(&result)),
            PPTokenFlags::empty(),
            location,
            result.len() as u16,
        ))
    }

    /// Paste tokens for ## operator
    fn paste_tokens(&mut self, left: &PPToken, right: &PPToken) -> Result<Vec<PPToken>, PPError> {
        // Get text of both tokens
        let left_buffer = self.source_manager.get_buffer(left.location.source_id());
        let left_start = left.location.offset() as usize;
        let left_end = left_start + left.length as usize;
        let left_text = if left_end <= left_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&left_buffer[left_start..left_end]) }
        } else {
            return Err(PPError::InvalidTokenPasting);
        };

        let right_buffer = self.source_manager.get_buffer(right.location.source_id());
        let right_start = right.location.offset() as usize;
        let right_end = right_start + right.length as usize;
        let right_text = if right_end <= right_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&right_buffer[right_start..right_end]) }
        } else {
            return Err(PPError::InvalidTokenPasting);
        };

        let pasted_text = format!("{}{}", left_text, right_text);

        // Create a virtual buffer containing the pasted text
        let virtual_buffer = pasted_text.clone().into_bytes();
        let virtual_id = self
            .source_manager
            .add_virtual_buffer(virtual_buffer, "<pasted-tokens>", None);

        // Create a temporary lexer to lex the pasted text
        let buffer = self.source_manager.get_buffer(virtual_id);
        let mut lexer = PPLexer::new(virtual_id, buffer.to_vec());

        let mut tokens = Vec::new();
        while let Some(token) = lexer.next_token() {
            if matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
                continue;
            }
            tokens.push(token);
        }

        // If the result is not a valid preprocessing token, the behavior is undefined.
        // We will return whatever tokens we got.
        Ok(tokens)
    }

    /// Expand tokens by rescanning for further macro expansion
    fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>) -> Result<(), PPError> {
        let mut i = 0;
        let max_expansions = 10000; // Safety limit to prevent infinite recursion

        while i < tokens.len() {
            let token = &tokens[i];
            match &token.kind {
                PPTokenKind::Identifier(symbol) if symbol.as_str() == "__LINE__" => {
                    let line = if let Some(presumed) = self.source_manager.get_presumed_location(token.location) {
                        presumed.0
                    } else {
                        1
                    };
                    let line_str = line.to_string();
                    let line_symbol = StringId::new(&line_str);
                    let number_token = PPToken::new(
                        PPTokenKind::Number(line_symbol),
                        PPTokenFlags::empty(),
                        token.location,
                        line_str.len() as u16,
                    );
                    tokens[i] = number_token;
                    i += 1;
                    continue;
                }
                PPTokenKind::Identifier(symbol) if symbol.as_str() == "__COUNTER__" => {
                    let val = self.get_next_counter();
                    let val_str = val.to_string();
                    let val_symbol = StringId::new(&val_str);
                    let number_token = PPToken::new(
                        PPTokenKind::Number(val_symbol),
                        PPTokenFlags::empty(),
                        token.location,
                        val_str.len() as u16,
                    );
                    tokens[i] = number_token;
                    i += 1;
                    continue;
                }
                PPTokenKind::Identifier(symbol) if symbol.as_str() == "__FILE__" => {
                    let filename = if let Some(presumed) = self.source_manager.get_presumed_location(token.location) {
                        if let Some(name) = presumed.2 {
                            format!("\"{}\"", name)
                        } else if let Some(file_info) = self.source_manager.get_file_info(token.location.source_id()) {
                            format!("\"{}\"", file_info.path.display())
                        } else {
                            "\"<unknown>\"".to_string()
                        }
                    } else if let Some(file_info) = self.source_manager.get_file_info(token.location.source_id()) {
                        format!("\"{}\"", file_info.path.display())
                    } else {
                        "\"<unknown>\"".to_string()
                    };
                    let file_symbol = StringId::new(&filename);
                    let string_token = PPToken::new(
                        PPTokenKind::StringLiteral(file_symbol),
                        PPTokenFlags::empty(),
                        token.location,
                        filename.len() as u16,
                    );
                    tokens[i] = string_token;
                    i += 1;
                    continue;
                }
                PPTokenKind::Identifier(symbol) if symbol == &self.directive_keywords.defined => {
                    // Skip 'defined'
                    i += 1;
                    // Skip the next token(s) which is the macro name, possibly in parens
                    if i < tokens.len() {
                        if tokens[i].kind == PPTokenKind::LeftParen {
                            // defined(MACRO)
                            // Skip until matching RightParen
                            let mut depth = 1;
                            i += 1;
                            while i < tokens.len() && depth > 0 {
                                match tokens[i].kind {
                                    PPTokenKind::LeftParen => depth += 1,
                                    PPTokenKind::RightParen => depth -= 1,
                                    _ => {}
                                }
                                i += 1;
                            }
                        } else {
                            // defined MACRO
                            i += 1;
                        }
                    }
                    continue;
                }
                _ => {}
            }

            let symbol = match tokens[i].kind {
                PPTokenKind::Identifier(s) => s,
                _ => {
                    i += 1;
                    continue;
                }
            };
            if let Some(macro_info) = self.macros.get(&symbol).cloned()
                && macro_info.flags.contains(MacroFlags::FUNCTION_LIKE)
                && !macro_info.flags.contains(MacroFlags::DISABLED)
                && i + 1 < tokens.len()
                && tokens[i + 1].kind == PPTokenKind::LeftParen
            {
                // Find the end of arguments
                let mut paren_depth = 0;
                let mut j = i + 1;
                let mut end_j = None;
                while j < tokens.len() {
                    match tokens[j].kind {
                        PPTokenKind::LeftParen => paren_depth += 1,
                        PPTokenKind::RightParen => {
                            paren_depth -= 1;
                            if paren_depth == 0 {
                                end_j = Some(j);
                                break;
                            }
                        }
                        _ => {}
                    }
                    j += 1;
                }
                if let Some(end_j) = end_j {
                    // Parse arguments using indices
                    let mut args = Vec::new();
                    let mut current_arg = Vec::new();
                    let mut paren_depth = 0;
                    let mut k = i + 2;
                    while k < end_j {
                        match tokens[k].kind {
                            PPTokenKind::LeftParen => {
                                paren_depth += 1;
                                current_arg.push(tokens[k]);
                            }
                            PPTokenKind::RightParen => {
                                paren_depth -= 1;
                                current_arg.push(tokens[k]);
                            }
                            PPTokenKind::Comma if paren_depth == 0 => {
                                args.push(current_arg);
                                current_arg = Vec::new();
                            }
                            _ => {
                                current_arg.push(tokens[k]);
                            }
                        }
                        k += 1;
                    }
                    if !current_arg.is_empty() {
                        args.push(current_arg);
                    }
                    // Validate argument count
                    let expected_args = macro_info.parameter_list.len();
                    if args.len() != expected_args {
                        // For conditional expressions, just skip problematic macro expansions
                        i += 1;
                        continue;
                    }
                    // Pre-expand arguments (prescan)
                    let mut expanded_args = Vec::with_capacity(args.len());
                    for arg in &args {
                        let mut arg_clone = arg.clone();
                        // Handle potential error in argument expansion
                        match self.expand_tokens(&mut arg_clone) {
                            Ok(_) => expanded_args.push(arg_clone),
                            Err(_) => expanded_args.push(arg.clone()), // Fallback to unexpanded
                        }
                    }

                    // Substitute
                    let substituted = match self.substitute_macro(&macro_info, &args, &expanded_args) {
                        Ok(substituted) => substituted,
                        Err(_) => {
                            // For conditional expressions, skip problematic substitutions
                            i += 1;
                            continue;
                        }
                    };

                    // Fix: Map substituted tokens to a virtual buffer to prevent leakage of internal locations
                    // (e.g. <pasted-tokens>) into the output stream.
                    let replacement_text = self.tokens_to_string(&substituted);
                    let virtual_buffer = replacement_text.into_bytes();
                    let virtual_id = self.source_manager.add_virtual_buffer(
                        virtual_buffer,
                        &format!("macro_{}", symbol.as_str()),
                        Some(token.location),
                    );

                    let mut remapped_tokens = Vec::with_capacity(substituted.len());
                    let mut offset = 0u32;

                    for original_token in &substituted {
                        let token_text = original_token.get_text();
                        let token_len = token_text.len() as u16;

                        let new_token = PPToken::new(
                            original_token.kind,
                            original_token.flags | PPTokenFlags::MACRO_EXPANDED,
                            SourceLoc::new(virtual_id, offset),
                            token_len,
                        );
                        remapped_tokens.push(new_token);
                        offset += token_len as u32;
                    }

                    // Use remapped tokens for subsequent processing
                    let substituted = remapped_tokens;

                    // Safety check for excessive expansions
                    let expansion_count = substituted.len();
                    if expansion_count > max_expansions {
                        // For conditional expressions, skip problematic expansions
                        i += 1;
                        continue;
                    }

                    // Replace i..end_j+1 with substituted
                    tokens.splice(i..end_j + 1, substituted);
                    // Mark as used
                    if let Some(m) = self.macros.get_mut(&symbol) {
                        m.flags |= MacroFlags::USED;
                    }
                    // Temporarily disable
                    if let Some(m) = self.macros.get_mut(&symbol) {
                        m.flags |= MacroFlags::DISABLED;
                    }
                    // Recurse
                    if self.expand_tokens(tokens).is_err() {
                        // For conditional expressions, continue even if recursion fails
                    }
                    // Re-enable
                    if let Some(m) = self.macros.get_mut(&symbol) {
                        m.flags.remove(MacroFlags::DISABLED);
                    }
                    continue;
                }
            }

            // For object macros
            if let Some(expanded) = self.expand_macro(&tokens[i]).unwrap_or(None) {
                tokens.splice(i..i + 1, expanded);
                continue;
            }

            // Check for _Pragma in the expanded stream
            if let PPTokenKind::Identifier(symbol) = tokens[i].kind
                && symbol.as_str() == "_Pragma"
            {
                // Need at least 3 more tokens: ( "string" )
                if i + 3 < tokens.len()
                    && tokens[i + 1].kind == PPTokenKind::LeftParen
                    && matches!(tokens[i + 2].kind, PPTokenKind::StringLiteral(_))
                    && tokens[i + 3].kind == PPTokenKind::RightParen
                    && let PPTokenKind::StringLiteral(sym) = tokens[i + 2].kind
                {
                    let content = self.destringize(sym.as_str());
                    self.perform_pragma(&content);
                    // Remove the 4 tokens
                    tokens.drain(i..i + 4);
                    // Do not increment i, as we removed tokens
                    continue;
                }
            }

            i += 1;
        }

        Ok(())
    }

    /// Skip current directive tokens until EOD
    fn skip_directive(&mut self) -> Result<(), PPError> {
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
        }
        Ok(())
    }

    /// Push a conditional that is lazily skipped (nested in a skipped block)
    fn push_skipped_conditional(&mut self) {
        // Equivalent to handle_if_directive(false)
        let info = PPConditionalInfo {
            was_skipping: self.is_currently_skipping(),
            found_else: false,
            found_non_skipping: false, // Condition treated as false
        };
        self.conditional_stack.push(info);
        // Force skipping for this level
        self.set_skipping(true);
    }

    /// Check if we should evaluate conditional expression (e.g. for #elif)
    fn should_evaluate_conditional(&self) -> bool {
        // We should evaluate ONLY if no parent is skipping
        // The current level (which we are about to replace with elif) is at index len()-1.
        // The parent is at index len()-2.
        if self.conditional_stack.len() > 1 {
            let parent_index = self.conditional_stack.len() - 2;
            let parent_skipping = self.conditional_stack[parent_index].was_skipping;
            if parent_skipping {
                return false;
            }
        }

        // And if we haven't found a true branch in this level yet
        if let Some(current) = self.conditional_stack.last() {
            !current.found_non_skipping
        } else {
            false
        }
    }
}
