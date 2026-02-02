use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::lang_options::LangOptions;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use hashbrown::HashMap;
use std::collections::{HashSet, VecDeque};

use super::pp_lexer::PPLexer;
use crate::pp::interpreter::Interpreter;
use crate::pp::{HeaderSearch, PPToken, PPTokenFlags, PPTokenKind};
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
    has_include: StringId,
    line_macro: StringId,
    file_macro: StringId,
    counter_macro: StringId,
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
            has_include: StringId::new("__has_include"),
            line_macro: StringId::new("__LINE__"),
            file_macro: StringId::new("__FILE__"),
            counter_macro: StringId::new("__COUNTER__"),
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

    /// Get the interned symbol for the "__has_include" operator
    pub(crate) fn has_include_symbol(&self) -> StringId {
        self.has_include
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
pub(crate) struct PPConditionalInfo {
    was_skipping: bool,
    found_else: bool,
    found_non_skipping: bool,
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
    pub current_time: Option<DateTime<Utc>>,
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
            current_time: None,
        }
    }
}

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    sm: &'src mut SourceManager,
    diag: &'src mut DiagnosticEngine,
    lang_opts: LangOptions,
    target: Triple,

    // Pre-interned directive keywords for fast comparison
    directive_keywords: DirectiveKeywordTable,

    // Macro management
    macros: HashMap<StringId, MacroInfo>,
    macro_stack: HashMap<StringId, Vec<Option<MacroInfo>>>,

    // Include management
    once_included: HashSet<SourceId>,

    // Conditional compilation state
    conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    include_stack: Vec<IncludeStackInfo>,
    header_search: HeaderSearch,
    built_in_headers: HashMap<&'static str, &'static str>,
    built_in_file_ids: HashMap<String, SourceId>,

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
    #[error("Pragma error: {0}")]
    PragmaError(String),
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
            PPError::PragmaError(_) => DiagnosticLevel::Error,
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

        let mut preprocessor = Preprocessor {
            sm: source_manager,
            diag,
            lang_opts: config.lang_options,
            directive_keywords: DirectiveKeywordTable::new(),
            macros: HashMap::new(),
            macro_stack: HashMap::new(),
            once_included: HashSet::new(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            built_in_headers,
            built_in_file_ids: HashMap::new(),
            lexer_stack: Vec::new(),
            pending_tokens: VecDeque::new(),
            include_depth: 0,
            max_include_depth: config.max_include_depth,
            target: config.target.clone(),
            counter: 0,
        };

        // Initialize built-in headers
        for (name, content) in &preprocessor.built_in_headers {
            let source_id = preprocessor.sm.add_buffer(
                content.as_bytes().to_vec(),
                name,
                None, // No include location for initialization
            );
            preprocessor.built_in_file_ids.insert(name.to_string(), source_id);
        }

        preprocessor.initialize_builtin_macros(config.current_time);
        preprocessor
    }

    /// Try to expand a magic macro (e.g. __LINE__, __FILE__, __COUNTER__)
    fn try_expand_magic_macro(&mut self, token: &PPToken) -> Option<PPToken> {
        let PPTokenKind::Identifier(symbol) = token.kind else {
            return None;
        };

        let (kind, text) = if symbol == self.directive_keywords.line_macro {
            let line = self.sm.get_presumed_location(token.location).map(|p| p.0).unwrap_or(1);
            let text = line.to_string();
            (PPTokenKind::Number(StringId::new(&text)), text)
        } else if symbol == self.directive_keywords.file_macro {
            let filename = self
                .sm
                .get_presumed_location(token.location)
                .and_then(|p| p.2)
                .unwrap_or("<unknown>");
            let text = format!("\"{}\"", filename);
            (PPTokenKind::StringLiteral(StringId::new(&text)), text)
        } else if symbol == self.directive_keywords.counter_macro {
            let text = self.get_next_counter().to_string();
            (PPTokenKind::Number(StringId::new(&text)), text)
        } else {
            return None;
        };

        Some(PPToken::text(kind, PPTokenFlags::empty(), token.location, &text))
    }

    /// Get the next value for __COUNTER__
    fn get_next_counter(&mut self) -> u32 {
        let val = self.counter;
        self.counter += 1;
        val
    }

    /// Initialize built-in macros
    fn initialize_builtin_macros(&mut self, current_time: Option<DateTime<Utc>>) {
        let now: DateTime<Utc> = current_time.unwrap_or_else(Utc::now);

        // __DATE__
        let date_str = format!("\"{:02} {:02} {}\"", now.format("%b"), now.day(), now.year());
        let date_tokens = self.tokenize_string(&date_str);
        self.define_builtin_macro("__DATE__", date_tokens);

        // __TIME__
        let time_str = format!("\"{:02}:{:02}:{:02}\"", now.hour(), now.minute(), now.second());
        let time_tokens = self.tokenize_string(&time_str);
        self.define_builtin_macro("__TIME__", time_tokens);

        // Other built-ins
        self.define_builtin_macro_one("__STDC__");

        // Target specific macros
        // Architecture
        match self.target.architecture {
            Architecture::X86_64 => {
                self.define_builtin_macro_one("__x86_64__");
                self.define_builtin_macro_one("__x86_64");
                self.define_builtin_macro_one("__amd64__");
                self.define_builtin_macro_one("__amd64");
            }
            Architecture::X86_32(_) => {
                self.define_builtin_macro_one("__i386__");
                self.define_builtin_macro_one("__i386");
            }
            Architecture::Aarch64(_) => {
                self.define_builtin_macro_one("__aarch64__");
            }
            Architecture::Arm(_) => {
                self.define_builtin_macro_one("__arm__");
            }
            _ => {}
        }

        // Pointer width
        if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(64) == 64 {
            self.define_builtin_macro_one("__LP64__");
            self.define_builtin_macro_one("_LP64");
        } else {
            self.define_builtin_macro_one("__ILP32__");
            self.define_builtin_macro_one("_ILP32");
        }

        // OS
        match self.target.operating_system {
            OperatingSystem::Linux => {
                self.define_builtin_macro_one("__linux__");
                self.define_builtin_macro_one("__linux");
                self.define_builtin_macro_one("__unix__");
                self.define_builtin_macro_one("__unix");
                self.define_builtin_macro_one("__ELF__");
                self.define_builtin_macro_one("__gnu_linux__");
            }
            OperatingSystem::Darwin(_) => {
                self.define_builtin_macro_one("__APPLE__");
                self.define_builtin_macro_one("__MACH__");
            }
            OperatingSystem::Windows => {
                self.define_builtin_macro_one("_WIN32");
                if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(32) == 64 {
                    self.define_builtin_macro_one("_WIN64");
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
            self.define_builtin_macro_one("__STDC_HOSTED__");
            self.define_builtin_macro_one("__STDC_MB_MIGHT_NEQ_WC__");
            self.define_builtin_macro_one("__STDC_IEC_559__");
            self.define_builtin_macro_one("__STDC_IEC_559_COMPLEX__");
            self.define_builtin_macro(
                "__STDC_ISO_10646__",
                vec![PPToken::new(
                    PPTokenKind::Number(StringId::new("201103L")),
                    PPTokenFlags::empty(),
                    SourceLoc::builtin(),
                    7,
                )],
            );
            self.define_builtin_macro_one("__STDC_UTF_16__");
            self.define_builtin_macro_one("__STDC_UTF_32__");
        }
    }

    /// Helper to define a built-in macro with value "1"
    fn define_builtin_macro_one(&mut self, name: &str) {
        self.define_builtin_macro(
            name,
            vec![PPToken::simple(
                PPTokenKind::Number(StringId::new("1")),
                SourceLoc::builtin(),
            )],
        );
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

    /// Get the interned symbol for the "__has_include" operator
    pub(crate) fn has_include_symbol(&self) -> StringId {
        self.directive_keywords.has_include_symbol()
    }

    /// Get the text associated with a token
    pub(crate) fn get_token_text(&self, token: &PPToken) -> &str {
        let buffer = self.sm.get_buffer(token.location.source_id());
        let start = token.location.offset() as usize;
        let end = start + token.length as usize;
        if end <= buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) }
        } else {
            ""
        }
    }

    /// Convert a list of tokens to a path string
    fn tokens_to_path_string(&self, tokens: &[PPToken]) -> String {
        // Bolt ⚡: Use a two-pass approach to build the path string efficiently.
        // This avoids multiple reallocations from push_str in a loop, a known
        // performance anti-pattern in this codebase.
        // 1. Calculate the total length of the path.
        let total_len = tokens.iter().map(|part| part.length as usize).sum();

        // 2. Allocate the string with the exact capacity.
        let mut path = String::with_capacity(total_len);

        // 3. Populate the string.
        for part in tokens.iter() {
            let buffer = self.sm.get_buffer(part.location.source_id());
            let start = part.location.offset() as usize;
            let end = start + part.length as usize;
            if end <= buffer.len() {
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                path.push_str(text);
            }
        }
        path
    }

    /// Check if a header exists
    pub(crate) fn check_header_exists(&self, path: &str, is_angled: bool) -> bool {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        if is_angled && self.built_in_headers.contains_key(path) {
            return true;
        }

        self.header_search.resolve_path(path, is_angled, current_dir).is_some()
            || (!is_angled && self.sm.get_file_id(path).is_some())
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
        let buffer_len = self.sm.get_buffer(source_id).len() as u32;
        let buffer = self.sm.get_buffer(source_id).to_vec();

        self.lexer_stack.push(PPLexer::new(source_id, buffer));
        self.sm.calculate_line_starts(source_id);

        let mut result_tokens = Vec::new();

        while let Some(token) = self.lex_token() {
            match token.kind {
                // Handle directive
                PPTokenKind::Hash if !token.flags.contains(PPTokenFlags::MACRO_EXPANDED) => {
                    self.handle_directive()?;
                }
                // Skip tokens when in conditional compilation skip mode
                _ if self.is_currently_skipping() => continue,
                // Skip Eod tokens
                PPTokenKind::Eod => continue,
                // Handle identifiers (macros, magic macros, _Pragma)
                PPTokenKind::Identifier(symbol) => {
                    let sym_str = symbol.as_str();
                    if let Some(magic) = self.try_expand_magic_macro(&token) {
                        result_tokens.push(magic);
                    } else if sym_str == "_Pragma" {
                        self.handle_pragma_operator()?;
                    } else if self.is_recursive_expansion(token.location, sym_str) {
                        result_tokens.push(token);
                    } else if let Some(expanded) = self.expand_macro(&token)? {
                        for t in expanded.into_iter().rev() {
                            self.pending_tokens.push_front(t);
                        }
                    } else {
                        result_tokens.push(token);
                    }
                }
                // All other tokens
                _ => result_tokens.push(token),
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
            let loc = self.get_current_location();
            self.report_diagnostic_simple(
                DiagnosticLevel::Error,
                "Unclosed preprocessor conditional directive",
                SourceSpan::new(loc, loc),
                Some("unclosed_conditional".to_string()),
                vec!["Expected #endif before end of file".to_string()],
            );
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
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
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
        match self.expand_tokens(&mut expanded_tokens, true) {
            Ok(_) => {}
            Err(_e) => {
                // If macro expansion fails, emit diagnostic and treat as false
                let span = if !tokens.is_empty() {
                    SourceSpan::new(tokens[0].location, tokens.last().unwrap().location)
                } else {
                    let loc = self.get_current_location();
                    SourceSpan::new(loc, loc)
                };
                self.report_diagnostic_simple(
                    DiagnosticLevel::Warning,
                    "Failed to expand macros in conditional expression".to_string(),
                    span,
                    Some("macro_expansion_failed".to_string()),
                    vec!["Expression will be treated as false".to_string()],
                );
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
            Ok(val) => Ok(val.is_truthy()),
            Err(_) => {
                // For complex expressions that can't be parsed, emit a warning and treat as false
                let span = if !tokens.is_empty() {
                    SourceSpan::new(tokens[0].location, tokens.last().unwrap().location)
                } else {
                    let loc = self.get_current_location();
                    SourceSpan::new(loc, loc)
                };
                self.report_diagnostic_simple(
                    DiagnosticLevel::Warning,
                    "Invalid conditional expression in preprocessor directive".to_string(),
                    span,
                    Some("invalid_conditional_expression".to_string()),
                    vec!["Expression will be treated as false".to_string()],
                );
                // Return false for unparseable expressions to allow compilation to continue
                Ok(false)
            }
        }
    }

    /// Lex the next token
    fn pop_finished_lexer(&mut self) -> bool {
        // EOF reached, pop the lexer
        let popped_lexer = self.lexer_stack.pop().unwrap();

        // If this was an included file, pop from include stack and decrement depth.
        if let Some(include_info) = self.include_stack.last()
            && include_info.file_id == popped_lexer.source_id
        {
            self.include_stack.pop();
            self.include_depth -= 1;
        }

        // ⚡ Bolt: Use `take_line_starts` to move the line_starts vector
        // instead of cloning it. This is a performance optimization that
        // avoids a potentially large allocation when a file is finished lexing.
        self.sm
            .set_line_starts(popped_lexer.source_id, popped_lexer.take_line_starts());

        !self.lexer_stack.is_empty()
    }

    /// Lex the next token
    fn lex_token(&mut self) -> Option<PPToken> {
        if let Some(token) = self.pending_tokens.pop_front() {
            return Some(token);
        }

        loop {
            if let Some(lexer) = self.lexer_stack.last_mut() {
                if let Some(token) = lexer.next_token() {
                    if token.flags.contains(PPTokenFlags::HAS_INVALID_UCN) {
                        self.report_diagnostic_simple(
                            DiagnosticLevel::Error,
                            "Invalid universal character name in literal".to_string(),
                            SourceSpan::new(token.location, token.location),
                            Some("invalid_ucn".to_string()),
                            Vec::new(),
                        );
                    }
                    return Some(token);
                } else {
                    // Current lexer finished
                    if !self.pop_finished_lexer() {
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
                        self.report_diagnostic_simple(
                            DiagnosticLevel::Error,
                            format!("Invalid preprocessor directive '{name}'"),
                            SourceSpan::new(token.location, token.location),
                            Some("invalid_directive".to_string()),
                            vec!["Valid directives include #define, #include, #if, #ifdef, #ifndef, #elif, #else, #endif, #line, #pragma, #error, #warning".to_string()],
                        );
                        Err(PPError::InvalidDirective)
                    }
                }
            }
            PPTokenKind::Eod => Ok(()),
            _ => {
                self.report_diagnostic_simple(
                    DiagnosticLevel::Error,
                    "Invalid preprocessor directive".to_string(),
                    SourceSpan::new(token.location, token.location),
                    Some("invalid_directive".to_string()),
                    vec!["Valid directives include #define, #include, #if, #ifdef, #ifndef, #elif, #else, #endif, #line, #pragma, #error, #warning".to_string()],
                );
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
    pub(crate) fn destringize(&self, full_str: &str) -> String {
        crate::ast::literal_parsing::unescape_string(&full_str[1..full_str.len() - 1])
    }

    /// Tokenize the content of a pragma directive
    fn tokenize_pragma_content(&mut self, pragma_content: &str) -> Vec<PPToken> {
        // Create a buffer for the pragma content
        let source_id = self
            .sm
            .add_buffer(pragma_content.as_bytes().to_vec(), "<_Pragma>", None);
        let buffer = self.sm.get_buffer(source_id);
        let mut temp_lexer = PPLexer::new(source_id, buffer.to_vec());

        // Collect all tokens from the pragma content
        let mut tokens = Vec::new();
        while let Some(token) = temp_lexer.next_token() {
            if matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
                continue;
            }
            tokens.push(token);
        }

        // Determine location for the synthetic EOD
        let eod_loc = if let Some(last) = tokens.last() {
            last.location
        } else {
            SourceLoc::new(source_id, 0)
        };

        // Append EOD token to mark end of pragma
        tokens.push(PPToken::new(PPTokenKind::Eod, PPTokenFlags::empty(), eod_loc, 0));

        tokens
    }

    /// Perform the action of a pragma directive
    fn perform_pragma(&mut self, pragma_content: &str) {
        let tokens = self.tokenize_pragma_content(pragma_content);

        // Push to pending_tokens in reverse order so they come out in correct order
        for token in tokens.into_iter().rev() {
            self.pending_tokens.push_front(token);
        }

        // Execute pragma handler
        // handle_pragma will consume tokens from pending_tokens
        if self.handle_pragma().is_err() {
            // If handle_pragma failed (e.g. unknown pragma), it might not have consumed all tokens.
            // We must consume the remaining tokens of this pragma until EOD to ensure they don't leak.
            while let Some(token) = self.lex_token() {
                if token.kind == PPTokenKind::Eod {
                    break;
                }
            }
        }
    }

    /// Handle #define directive
    fn parse_define_args(&mut self, name: &str) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
        let Some(token) = self.lex_token() else {
            return Ok((MacroFlags::empty(), Vec::new(), None));
        };

        if token.kind == PPTokenKind::LeftParen && !token.flags.contains(PPTokenFlags::LEADING_SPACE) {
            let first_param = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;

            if matches!(
                first_param.kind,
                PPTokenKind::RightParen | PPTokenKind::Identifier(_) | PPTokenKind::Ellipsis
            ) {
                self.pending_tokens.push_front(first_param);
                return self.parse_macro_definition_params(name);
            }

            self.pending_tokens.push_front(first_param);
            self.pending_tokens.push_front(token);
            return Ok((MacroFlags::empty(), Vec::new(), None));
        }

        self.pending_tokens.push_front(token);
        Ok((MacroFlags::empty(), Vec::new(), None))
    }

    fn check_macro_redefinition(&mut self, name: StringId, name_token: &PPToken, macro_info: &MacroInfo) -> bool {
        if let Some(existing) = self.macros.get(&name) {
            if existing.flags.contains(MacroFlags::BUILTIN) {
                self.report_diagnostic_simple(
                    DiagnosticLevel::Warning,
                    format!("Redefinition of built-in macro '{}'", name.as_str()),
                    SourceSpan::new(name_token.location, name_token.location),
                    Some("builtin_macro_redefinition".to_string()),
                    Vec::new(),
                );
                return false;
            }

            // Check if definition is different
            let is_different = existing.flags != macro_info.flags
                || existing.parameter_list != macro_info.parameter_list
                || existing.variadic_arg != macro_info.variadic_arg
                || existing.tokens.len() != macro_info.tokens.len()
                || existing
                    .tokens
                    .iter()
                    .zip(macro_info.tokens.iter())
                    .any(|(a, b)| a.kind != b.kind || a.flags != b.flags);

            if is_different {
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
        true
    }

    fn handle_define(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };

        let (flags, params, variadic) = self.parse_define_args(name.as_str())?;

        // Collect body tokens
        // Use collect_tokens_until_eod which handles the loop and checking for Eod
        let tokens = self.collect_tokens_until_eod();

        // Store the macro
        let macro_info = MacroInfo {
            location: name_token.location,
            flags,
            tokens,
            parameter_list: params,
            variadic_arg: variadic,
        };

        if self.check_macro_redefinition(name, &name_token, &macro_info) {
            self.macros.insert(name, macro_info);
        }
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPError> {
        let name_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let name = match name_token.kind {
            PPTokenKind::Identifier(sym) => sym,
            _ => return Err(PPError::ExpectedIdentifier),
        };

        if let Some(existing) = self.macros.get(&name)
            && existing.flags.contains(MacroFlags::BUILTIN)
        {
            self.report_diagnostic_simple(
                DiagnosticLevel::Warning,
                format!("Undefining built-in macro '{}'", name.as_str()),
                SourceSpan::new(name_token.location, name_token.location),
                Some("undef_builtin_macro".to_string()),
                Vec::new(),
            );
            self.expect_eod()?;
            return Ok(());
        }

        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn handle_include(&mut self) -> Result<(), PPError> {
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let mut eod_consumed = false;

        let (path_str, is_angled) = match token.kind {
            PPTokenKind::StringLiteral(symbol) => {
                let s = symbol.as_str();
                let path = s
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .ok_or(PPError::InvalidIncludePath)?;
                (path.to_string(), false)
            }
            PPTokenKind::Less => {
                let mut path_parts = Vec::new();
                while let Some(t) = self.lex_token() {
                    if t.kind == PPTokenKind::Greater {
                        break;
                    }
                    path_parts.push(t);
                }
                (self.tokens_to_path_string(&path_parts), true)
            }
            _ => {
                // Computed include
                let mut tokens = vec![token];
                while let Some(t) = self.lex_token() {
                    if t.kind == PPTokenKind::Eod {
                        break;
                    }
                    tokens.push(t);
                }
                eod_consumed = true;
                self.expand_tokens(&mut tokens, false)?;

                if tokens.is_empty() {
                    return Err(PPError::InvalidIncludePath);
                }

                let first = &tokens[0];
                match first.kind {
                    PPTokenKind::StringLiteral(symbol) => {
                        if tokens.len() > 1 {
                            self.report_extra_tokens_after_directive(
                                tokens[1].location,
                                tokens.last().unwrap().location,
                            );
                            return Err(PPError::ExpectedEod);
                        }
                        let s = symbol.as_str();
                        let path = s
                            .strip_prefix('"')
                            .and_then(|s| s.strip_suffix('"'))
                            .ok_or(PPError::InvalidIncludePath)?;
                        (path.to_string(), false)
                    }
                    PPTokenKind::Less => {
                        let mut path_parts = Vec::new();
                        let mut greater_idx = None;
                        for (i, t) in tokens.iter().enumerate().skip(1) {
                            if t.kind == PPTokenKind::Greater {
                                greater_idx = Some(i);
                                break;
                            }
                            path_parts.push(*t);
                        }
                        let idx = greater_idx.ok_or(PPError::InvalidIncludePath)?;
                        if idx + 1 < tokens.len() {
                            self.report_extra_tokens_after_directive(
                                tokens[idx + 1].location,
                                tokens.last().unwrap().location,
                            );
                            return Err(PPError::ExpectedEod);
                        }
                        (self.tokens_to_path_string(&path_parts), true)
                    }
                    _ => return Err(PPError::InvalidIncludePath),
                }
            }
        };

        if self.include_depth >= self.max_include_depth {
            return Err(PPError::IncludeDepthExceeded);
        }

        let include_source_id = self.resolve_include_path(&path_str, is_angled, token.location)?;

        if self.once_included.contains(&include_source_id) {
            return Ok(());
        }

        self.include_stack.push(IncludeStackInfo {
            file_id: include_source_id,
        });

        if !eod_consumed {
            self.expect_eod()?;
        }

        let buffer = self.sm.get_buffer(include_source_id);
        self.lexer_stack.push(PPLexer::new(include_source_id, buffer.to_vec()));
        self.include_depth += 1;

        Ok(())
    }

    fn resolve_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPError> {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        let resolved = self.header_search.resolve_path(path, is_angled, current_dir);

        if let Some(path_buf) = resolved {
            return self.sm.add_file_from_path(&path_buf, Some(loc)).map_err(|_| {
                self.report_include_not_found(path, loc);
                PPError::FileNotFound
            });
        }

        let fallback_id = if is_angled {
            self.built_in_file_ids.get(path).copied()
        } else {
            self.sm.get_file_id(path)
        };

        if let Some(id) = fallback_id {
            Ok(id)
        } else {
            self.report_include_not_found(path, loc);
            Err(PPError::FileNotFound)
        }
    }

    fn report_include_not_found(&mut self, path: &str, loc: SourceLoc) {
        self.report_diagnostic_simple(
            DiagnosticLevel::Error,
            format!("Include file '{}' not found", path),
            SourceSpan::new(loc, loc),
            Some("include_file_not_found".to_string()),
            vec!["Check the include path and ensure the file exists".to_string()],
        );
    }

    fn report_extra_tokens_after_directive(&mut self, start: SourceLoc, end: SourceLoc) {
        self.report_diagnostic_simple(
            DiagnosticLevel::Error,
            "Extra tokens at end of preprocessor directive",
            SourceSpan::new(start, end),
            Some("extra_tokens_directive".to_string()),
            vec![],
        );
    }
    fn handle_if_directive(&mut self, condition: bool) -> Result<(), PPError> {
        self.conditional_stack.push(PPConditionalInfo {
            was_skipping: !condition,
            found_else: false,
            found_non_skipping: condition,
        });
        Ok(())
    }

    fn handle_conditional_def(&mut self, is_ifdef: bool) -> Result<(), PPError> {
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let PPTokenKind::Identifier(sym) = token.kind else {
            return Err(PPError::ExpectedIdentifier);
        };

        let condition = self.macros.contains_key(&sym) == is_ifdef;
        self.handle_if_directive(condition)?;
        self.expect_eod()
    }

    fn handle_ifdef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(true)
    }

    fn handle_ifndef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(false)
    }

    fn handle_elif_directive(&mut self, condition: bool, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            self.report_unmatched_directive("#elif", location);
            return Err(PPError::ElifWithoutIf);
        }
        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            self.report_invalid_conditional_order("#elif", location);
            return Err(PPError::UnmatchedElif);
        }

        let should_process = !current.found_non_skipping && condition;
        if should_process {
            current.found_non_skipping = true;
        }
        current.was_skipping = !should_process;

        Ok(())
    }

    fn handle_else(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            self.report_unmatched_directive("#else", location);
            return Err(PPError::ElseWithoutIf);
        }
        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            self.report_invalid_conditional_order("#else", location);
            return Err(PPError::UnmatchedElse);
        }

        current.found_else = true;
        let should_process = !current.found_non_skipping;
        current.was_skipping = !should_process;

        self.expect_eod()
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.pop().is_none() {
            self.report_unmatched_directive("#endif", location);
            return Err(PPError::UnmatchedEndif);
        }
        self.expect_eod()
    }

    fn report_unmatched_directive(&mut self, name: &str, location: SourceLoc) {
        let (code, msg, hint) = match name {
            "#elif" => (
                "elif_without_if",
                "#elif without #if",
                "#elif must be preceded by #if, #ifdef, or #ifndef",
            ),
            "#else" => (
                "else_without_if",
                "#else without #if",
                "#else must be preceded by #if, #ifdef, or #ifndef",
            ),
            "#endif" => (
                "unmatched_endif",
                "Unmatched #endif",
                "#endif must be preceded by #if, #ifdef, or #ifndef",
            ),
            _ => ("unmatched_directive", "Unmatched directive", ""),
        };

        self.report_diagnostic_simple(
            DiagnosticLevel::Error,
            msg,
            SourceSpan::new(location, location),
            Some(code.to_string()),
            vec![hint.to_string()],
        );
    }

    fn report_invalid_conditional_order(&mut self, name: &str, location: SourceLoc) {
        let (code, msg, hint) = match name {
            "#elif" => (
                "elif_after_else",
                "#elif after #else",
                "#else must be the last directive in a conditional block",
            ),
            "#else" => (
                "multiple_else",
                "Multiple #else directives",
                "A conditional block can only have one #else",
            ),
            _ => ("invalid_order", "Invalid conditional order", ""),
        };

        self.report_diagnostic_simple(
            DiagnosticLevel::Error,
            msg,
            SourceSpan::new(location, location),
            Some(code.to_string()),
            vec![hint.to_string()],
        );
    }
    fn collect_tokens_until_eod(&mut self) -> Vec<PPToken> {
        let mut tokens = Vec::new();
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }
        tokens
    }

    fn parse_line_directive_args(&self, tokens: &[PPToken]) -> Result<(u32, Option<String>), PPError> {
        let [first, rest @ ..] = tokens else {
            return Err(PPError::InvalidLineDirective);
        };

        let PPTokenKind::Number(symbol) = &first.kind else {
            return Err(PPError::InvalidLineDirective);
        };

        let line_num = symbol
            .as_str()
            .parse::<u32>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or(PPError::InvalidLineDirective)?;

        let filename = match rest {
            [] => None,
            [t] => {
                let PPTokenKind::StringLiteral(symbol) = &t.kind else {
                    return Err(PPError::InvalidLineDirective);
                };
                let s = symbol.as_str();
                let path = s
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .ok_or(PPError::InvalidLineDirective)?;
                Some(path.to_string())
            }
            _ => return Err(PPError::InvalidLineDirective),
        };

        Ok((line_num, filename))
    }

    fn handle_line(&mut self) -> Result<(), PPError> {
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        // Collect tokens until end of line
        let mut tokens = self.collect_tokens_until_eod();

        if tokens.is_empty() {
            return Err(PPError::InvalidLineDirective);
        }

        // Expand macros in tokens
        self.expand_tokens(&mut tokens, false)?;

        let (logical_line, logical_file) = self.parse_line_directive_args(&tokens)?;

        // Get current physical line (where #line directive appears)
        let physical_line = start_line;

        // The #line directive sets the line number for the following line,
        // so we need to adjust the logical_line for the entry
        let entry_logical_line = logical_line - 1;

        // Add entry to LineMap
        if let Some(lexer) = self.lexer_stack.last()
            && let Some(line_map) = self.sm.get_line_map_mut(lexer.source_id)
        {
            let entry = crate::source_manager::LineDirective::new(physical_line, entry_logical_line, logical_file);
            line_map.add_entry(entry);
        }

        Ok(())
    }
    fn handle_pragma(&mut self) -> Result<(), PPError> {
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let PPTokenKind::Identifier(symbol) = &token.kind else {
            self.report_diagnostic_simple(
                DiagnosticLevel::Error,
                "Invalid pragma directive",
                SourceSpan::new(token.location, token.location),
                Some("invalid_pragma".to_string()),
                vec!["Pragma directive requires an identifier".to_string()],
            );
            return Err(PPError::InvalidDirective);
        };

        let pragma_name = symbol.as_str();
        match pragma_name {
            "once" => {
                if let Some(lexer) = self.lexer_stack.last() {
                    self.once_included.insert(lexer.source_id);
                }
            }
            "push_macro" => self.handle_push_macro()?,
            "pop_macro" => self.handle_pop_macro()?,
            "message" => self.handle_pragma_message()?,
            "warning" => self.handle_pragma_warning()?,
            "error" => self.handle_pragma_error()?,
            _ => {
                self.report_diagnostic_simple(
                    DiagnosticLevel::Error,
                    format!("Unknown pragma '{}'", pragma_name),
                    SourceSpan::new(token.location, token.location),
                    Some("unknown_pragma".to_string()),
                    vec!["Supported pragmas: once, push_macro, pop_macro, message, warning, error".to_string()],
                );
                return Err(PPError::UnknownPragma(pragma_name.to_string()));
            }
        }

        self.collect_tokens_until_eod();
        Ok(())
    }

    fn parse_pragma_macro_name(&mut self) -> Result<StringId, PPError> {
        if self.lex_token().is_none_or(|t| t.kind != PPTokenKind::LeftParen) {
            return Err(PPError::InvalidDirective);
        }

        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        let PPTokenKind::StringLiteral(symbol) = token.kind else {
            return Err(PPError::InvalidDirective);
        };

        let s = symbol.as_str();
        let name = s
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .ok_or(PPError::InvalidDirective)?;

        if self.lex_token().is_none_or(|t| t.kind != PPTokenKind::RightParen) {
            return Err(PPError::InvalidDirective);
        }

        Ok(StringId::new(name))
    }

    fn handle_push_macro(&mut self) -> Result<(), PPError> {
        let name = self.parse_pragma_macro_name()?;

        let info = self.macros.get(&name).cloned();

        self.macro_stack.entry(name).or_default().push(info);

        Ok(())
    }

    fn handle_pop_macro(&mut self) -> Result<(), PPError> {
        let name = self.parse_pragma_macro_name()?;

        if let Some(stack) = self.macro_stack.get_mut(&name)
            && let Some(info_opt) = stack.pop()
        {
            if let Some(info) = info_opt {
                self.macros.insert(name, info);
            } else {
                self.macros.remove(&name);
            }
        }

        Ok(())
    }

    fn parse_pragma_message_content(&mut self) -> Result<String, PPError> {
        if self.lex_token().is_none_or(|t| t.kind != PPTokenKind::LeftParen) {
            return Err(PPError::InvalidDirective);
        }

        let mut tokens = Vec::new();
        let mut depth = 1;
        while let Some(t) = self.lex_token() {
            match t.kind {
                PPTokenKind::Eod => return Err(PPError::UnexpectedEndOfFile),
                PPTokenKind::LeftParen => depth += 1,
                PPTokenKind::RightParen
                    if {
                        depth -= 1;
                        depth == 0
                    } =>
                {
                    break;
                }
                _ => {}
            }
            tokens.push(t);
        }

        if depth > 0 {
            return Err(PPError::UnexpectedEndOfFile);
        }

        self.expand_tokens(&mut tokens, false)?;

        tokens.into_iter().try_fold(String::new(), |mut acc, t| {
            let PPTokenKind::StringLiteral(symbol) = t.kind else {
                return Err(PPError::InvalidDirective);
            };
            let s = symbol.as_str();
            if s.starts_with('"') && s.ends_with('"') {
                acc.push_str(&self.destringize(s));
                Ok(acc)
            } else {
                Err(PPError::InvalidDirective)
            }
        })
    }

    fn handle_pragma_diagnostic_message(&mut self, level: DiagnosticLevel) -> Result<(), PPError> {
        let message = self.parse_pragma_message_content()?;
        let loc = self.get_current_location();
        let diag = Diagnostic {
            level,
            message: message.clone(),
            span: SourceSpan::new(loc, loc),
            ..Default::default()
        };
        self.diag.report_diagnostic(diag);

        if level == DiagnosticLevel::Error {
            Err(PPError::PragmaError(message))
        } else {
            Ok(())
        }
    }

    fn handle_pragma_message(&mut self) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(DiagnosticLevel::Note)
    }

    fn handle_pragma_warning(&mut self) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(DiagnosticLevel::Warning)
    }

    fn handle_pragma_error(&mut self) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(DiagnosticLevel::Error)
    }

    fn handle_error(&mut self) -> Result<(), PPError> {
        // Note: Skipping is handled by caller (check_skipping_and_execute)

        let directive_location = self.get_current_location();
        let message = self.consume_rest_of_line_as_string();

        self.report_diagnostic_simple(
            DiagnosticLevel::Error,
            format!("#error directive: {}", message),
            SourceSpan::new(directive_location, directive_location),
            None,
            Vec::new(),
        );
        Err(PPError::ErrorDirective(message))
    }

    fn handle_warning(&mut self) -> Result<(), PPError> {
        // Note: Skipping is handled by caller (check_skipping_and_execute)

        let directive_location = self.get_current_location();
        let message = self.consume_rest_of_line_as_string();

        // For warning, we emit a diagnostic but don't stop compilation
        self.report_diagnostic_simple(
            DiagnosticLevel::Warning,
            message,
            SourceSpan::new(directive_location, directive_location),
            None,
            Vec::new(),
        );
        Ok(())
    }

    fn consume_rest_of_line_as_string(&mut self) -> String {
        // Optimization: Avoid multiple small allocations by calculating final string size first.
        // This follows the two-pass approach:
        // 1. Collect tokens for the line.
        // 2. Calculate the total length required for the string.
        // 3. Allocate a single string with the required capacity.
        // 4. Populate the string in a second pass over the tokens.
        let mut tokens = Vec::new();
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }

        if tokens.is_empty() {
            return String::new();
        }

        // Calculate total length
        let mut total_len = 0;
        for (i, token) in tokens.iter().enumerate() {
            total_len += token.length as usize;
            if i > 0 {
                total_len += 1; // For the space separator
            }
        }

        // Allocate and build the string
        let mut result = String::with_capacity(total_len);
        for (i, token) in tokens.iter().enumerate() {
            if i > 0 {
                result.push(' ');
            }
            let buffer = self.sm.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end <= buffer.len() {
                // This is safe because the lexer guarantees tokens are valid UTF-8.
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                result.push_str(text);
            }
        }

        result
    }

    /// Expand a macro if it exists
    pub(crate) fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPError> {
        let PPTokenKind::Identifier(symbol) = token.kind else {
            return Ok(None);
        };

        let macro_info = self
            .macros
            .get(&symbol)
            .filter(|m| !m.flags.contains(MacroFlags::DISABLED))
            .cloned();

        let Some(macro_info) = macro_info else {
            return Ok(None);
        };

        if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
            let next = self.lex_token();
            let is_call = matches!(next, Some(ref t) if t.kind == PPTokenKind::LeftParen);
            if let Some(t) = next {
                self.pending_tokens.push_front(t);
            }
            if !is_call {
                return Ok(None);
            }
        }

        if let Some(m) = self.macros.get_mut(&symbol) {
            m.flags |= MacroFlags::USED | MacroFlags::DISABLED;
        }

        let result = if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
            self.expand_function_macro(&macro_info, &symbol, token)
        } else {
            self.expand_object_macro(&macro_info, &symbol, token)
        };

        if let Some(m) = self.macros.get_mut(&symbol) {
            m.flags.remove(MacroFlags::DISABLED);
        }

        result.map(Some)
    }

    /// Helper to convert tokens to their string representation
    fn tokens_to_string(&self, tokens: &[PPToken]) -> String {
        // Bolt ⚡: Use a two-pass approach to build the string efficiently.
        // This avoids multiple reallocations from push_str in a loop.
        // 1. Calculate the total length of the string.
        let total_len: usize = tokens.iter().map(|t| t.get_text().len()).sum();

        // 2. Allocate the string with the exact capacity.
        let mut result = String::with_capacity(total_len);

        // 3. Populate the string.
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
        let mut expanded = self.create_virtual_buffer_tokens(&macro_info.tokens, symbol.as_str(), token.location);

        // Recursively expand any macros in the replacement
        self.expand_tokens(&mut expanded, false)?;

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
            self.expand_tokens(&mut arg_clone, false)?;
            expanded_args.push(arg_clone);
        }

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args, &expanded_args)?;

        // For Level B: Create a virtual buffer containing the substituted text
        let mut expanded = self.create_virtual_buffer_tokens(&substituted, symbol.as_str(), token.location);

        // Recursively expand any macros in the replacement
        self.expand_tokens(&mut expanded, false)?;

        Ok(expanded)
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(&mut self, macro_info: &MacroInfo) -> Result<Vec<Vec<PPToken>>, PPError> {
        let token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
        if token.kind != PPTokenKind::LeftParen {
            let span = SourceSpan::new(token.location, token.location);
            self.pending_tokens.push_front(token);
            return Err(PPError::InvalidMacroParameter { span });
        }

        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut depth = 0;

        while let Some(t) = self.lex_token() {
            match t.kind {
                PPTokenKind::Eof => break,
                PPTokenKind::LeftParen => {
                    depth += 1;
                    current_arg.push(t);
                }
                PPTokenKind::RightParen if depth > 0 => {
                    depth -= 1;
                    current_arg.push(t);
                }
                PPTokenKind::RightParen => {
                    if !current_arg.is_empty() || !args.is_empty() {
                        args.push(current_arg);
                    }

                    let expected = macro_info.parameter_list.len();
                    let valid = if macro_info.variadic_arg.is_some() {
                        args.len() >= expected
                    } else {
                        args.len() == expected
                    };

                    if valid {
                        return Ok(args);
                    }

                    return Err(PPError::InvalidMacroParameter {
                        span: SourceSpan::new(macro_info.location, macro_info.location),
                    });
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(t),
            }
        }

        Err(PPError::UnexpectedEndOfFile)
    }

    /// Helper to collect variadic arguments with commas inserted
    fn collect_variadic_args_with_commas(
        &mut self,
        args: &[Vec<PPToken>],
        start_index: usize,
        trigger_loc: SourceLoc,
    ) -> Vec<PPToken> {
        let mut result = Vec::new();
        let mut first = true;

        // We need a source for the comma token.
        // We create a virtual buffer for it to ensure stringification works correctly.
        // We only create it if we actually need a comma.
        let comma_source_id = if args.len() > start_index + 1 {
            Some(self.sm.add_virtual_buffer(b",".to_vec(), "<comma>", Some(trigger_loc)))
        } else {
            None
        };

        for arg in args.iter().skip(start_index) {
            if !first && let Some(sid) = comma_source_id {
                result.push(PPToken::new(
                    PPTokenKind::Comma,
                    PPTokenFlags::empty(),
                    SourceLoc::new(sid, 0),
                    1,
                ));
            }
            result.extend(arg.clone());
            first = false;
        }
        result
    }

    fn is_macro_param(&self, macro_info: &MacroInfo, symbol: StringId) -> bool {
        macro_info.variadic_arg == Some(symbol) || macro_info.parameter_list.contains(&symbol)
    }

    fn get_macro_param_tokens(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        args: &[Vec<PPToken>],
        location: SourceLoc,
    ) -> Option<Vec<PPToken>> {
        if let Some(idx) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
            return Some(args[idx].clone());
        }
        if macro_info.variadic_arg == Some(symbol) {
            let start = macro_info.parameter_list.len();
            return Some(self.collect_variadic_args_with_commas(args, start, location));
        }
        None
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
                PPTokenKind::Hash if i + 1 < macro_info.tokens.len() => {
                    let next = &macro_info.tokens[i + 1];
                    if let PPTokenKind::Identifier(sym) = next.kind
                        && let Some(arg) = self.get_macro_param_tokens(macro_info, sym, args, token.location)
                    {
                        result.push(self.stringify_tokens(&arg, token.location)?);
                        i += 2;
                        continue;
                    }
                }
                PPTokenKind::HashHash if i + 1 < macro_info.tokens.len() => {
                    let right_token = &macro_info.tokens[i + 1];
                    let left = result.pop().unwrap_or(*token);

                    let right_tokens = if let PPTokenKind::Identifier(sym) = right_token.kind {
                        self.get_macro_param_tokens(macro_info, sym, args, right_token.location)
                            .unwrap_or_else(|| vec![*right_token])
                    } else {
                        vec![*right_token]
                    };

                    if right_tokens.is_empty() {
                        // Potential GNU comma swallowing extension
                        let is_comma = left.kind == PPTokenKind::Comma;
                        let is_variadic = matches!(right_token.kind, PPTokenKind::Identifier(s) if macro_info.variadic_arg == Some(s));
                        if !(is_comma && is_variadic) {
                            result.push(left);
                        }
                    } else {
                        let pasted = self.paste_tokens(&left, &right_tokens[0])?;
                        result.extend(pasted);
                        result.extend(right_tokens.into_iter().skip(1));
                    }
                    i += 2;
                    continue;
                }
                PPTokenKind::Identifier(sym) if self.is_macro_param(macro_info, sym) => {
                    let next_is_hh =
                        i + 1 < macro_info.tokens.len() && macro_info.tokens[i + 1].kind == PPTokenKind::HashHash;
                    let src = if next_is_hh { args } else { expanded_args };
                    result.extend(
                        self.get_macro_param_tokens(macro_info, sym, src, token.location)
                            .unwrap(),
                    );
                }
                _ => result.push(*token),
            }
            i += 1;
        }

        Ok(result)
    }

    /// Stringify tokens for # operator
    pub(crate) fn stringify_tokens(&self, tokens: &[PPToken], location: SourceLoc) -> Result<PPToken, PPError> {
        // Bolt ⚡: Use a two-pass approach to build the stringified token efficiently.
        // This avoids multiple reallocations from push/push_str in a loop.
        // 1. Calculate the final length of the string, accounting for escaped characters.
        let mut total_len = 2; // For the opening and closing quotes
        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                total_len += 1; // For the space
            }
            let buffer = self.sm.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end > buffer.len() {
                return Err(PPError::InvalidStringification);
            }

            // ⚡ Bolt: Use byte-based iteration for correctness and speed.
            // Iterating over bytes is faster than UTF-8 chars and correctly calculates
            // the required byte capacity for multi-byte characters.
            let bytes = &buffer[start..end];
            for &b in bytes {
                match b {
                    b'"' | b'\\' => total_len += 2, // These will be escaped
                    _ => total_len += 1,
                }
            }
        }

        // 2. Allocate the string with the exact capacity.
        let mut result = String::with_capacity(total_len);
        result.push('"');

        // 3. Populate the string efficiently.
        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(' ');
            }

            let buffer = self.sm.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            // This check is already done above, but for safety we keep it.
            if end <= buffer.len() {
                // ⚡ Bolt: Chunked string building using slices.
                // This avoids the overhead of character-by-character iteration and pushing.
                let bytes = &buffer[start..end];
                let mut last_start = 0;
                for (j, &b) in bytes.iter().enumerate() {
                    if b == b'"' || b == b'\\' {
                        if j > last_start {
                            result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..j]) });
                        }
                        if b == b'"' {
                            result.push_str("\\\"");
                        } else {
                            result.push_str("\\\\");
                        }
                        last_start = j + 1;
                    }
                }
                if last_start < bytes.len() {
                    result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..]) });
                }
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
        let left_buffer = self.sm.get_buffer(left.location.source_id());
        let left_start = left.location.offset() as usize;
        let left_end = left_start + left.length as usize;
        let left_text = if left_end <= left_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&left_buffer[left_start..left_end]) }
        } else {
            return Err(PPError::InvalidTokenPasting);
        };

        let right_buffer = self.sm.get_buffer(right.location.source_id());
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
        let virtual_id = self.sm.add_virtual_buffer(virtual_buffer, "<pasted-tokens>", None);

        // Create a temporary lexer to lex the pasted text
        let buffer = self.sm.get_buffer(virtual_id);
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

    /// Finds the range of tokens between balanced parentheses, starting at `start_index`.
    /// Returns the end index (exclusive) if successful.
    fn find_balanced_paren_range(&self, tokens: &[PPToken], start_index: usize) -> Option<usize> {
        if start_index >= tokens.len() || tokens[start_index].kind != PPTokenKind::LeftParen {
            return None;
        }

        let mut depth = 0;
        for (i, t) in tokens.iter().enumerate().skip(start_index) {
            match t.kind {
                PPTokenKind::LeftParen => depth += 1,
                PPTokenKind::RightParen => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i + 1);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Collects macro arguments from a slice of tokens.
    fn collect_macro_args_from_slice(
        &self,
        tokens: &[PPToken],
        start_index: usize,
        end_index: usize,
    ) -> Vec<Vec<PPToken>> {
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut depth = 0;
        for token in &tokens[start_index..end_index] {
            match token.kind {
                PPTokenKind::LeftParen => {
                    depth += 1;
                    current_arg.push(*token);
                }
                PPTokenKind::RightParen => {
                    depth -= 1;
                    current_arg.push(*token);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(*token),
            }
        }
        if !current_arg.is_empty() {
            args.push(current_arg);
        }
        args
    }

    fn expand_has_include_computed_args(&mut self, args: &mut Vec<PPToken>) {
        let mut j = 0;
        let mut expansions = 0;
        while j < args.len() && expansions < 1000 {
            if j == 0
                && !args.is_empty()
                && (args[0].kind == PPTokenKind::Less || matches!(args[0].kind, PPTokenKind::StringLiteral(_)))
            {
                break;
            }
            if let Some(expanded) = self.expand_macro(&args[j]).unwrap_or_default() {
                args.splice(j..j + 1, expanded);
                expansions += 1;
                continue;
            }
            j += 1;
        }
    }

    fn try_handle_conditional_operator(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
    ) -> Result<Option<usize>, PPError> {
        let token = tokens[i];
        let PPTokenKind::Identifier(sym) = token.kind else {
            return Ok(None);
        };

        if sym == self.directive_keywords.defined {
            let next = i + 1;
            if next < tokens.len() {
                if tokens[next].kind == PPTokenKind::LeftParen {
                    if let Some(end) = self.find_balanced_paren_range(tokens, next) {
                        return Ok(Some(end));
                    }
                } else {
                    return Ok(Some(next + 1));
                }
            }
            return Ok(Some(next));
        }

        if sym == self.directive_keywords.has_include {
            let next = i + 1;
            if next < tokens.len() && tokens[next].kind == PPTokenKind::LeftParen {
                let arg_start = next + 1;
                if arg_start < tokens.len() {
                    match tokens[arg_start].kind {
                        PPTokenKind::Less | PPTokenKind::StringLiteral(_) => {
                            if let Some(end) = self.find_balanced_paren_range(tokens, next) {
                                return Ok(Some(end));
                            }
                        }
                        _ => {
                            // Computed form
                            if let Some(arg_end) = self.find_balanced_paren_range(tokens, next) {
                                let mut args = tokens[arg_start..arg_end - 1].to_vec();
                                self.expand_has_include_computed_args(&mut args);
                                let len = args.len();
                                tokens.splice(arg_start..arg_end - 1, args);
                                return Ok(Some(arg_start + len + 1));
                            }
                        }
                    }
                }
            }
            return Ok(Some(next));
        }

        Ok(None)
    }

    fn try_expand_function_macro_in_tokens(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
        in_conditional: bool,
    ) -> Result<bool, PPError> {
        let symbol_token = tokens[i];
        let PPTokenKind::Identifier(symbol) = symbol_token.kind else {
            return Ok(false);
        };

        let macro_info = self.macros.get(&symbol).cloned();
        let Some(macro_info) = macro_info else {
            return Ok(false);
        };

        if !macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) || macro_info.flags.contains(MacroFlags::DISABLED) {
            return Ok(false);
        }

        if i + 1 >= tokens.len() || tokens[i + 1].kind != PPTokenKind::LeftParen {
            return Ok(false);
        }

        let Some(end_j) = self.find_balanced_paren_range(tokens, i + 1) else {
            return Ok(false);
        };

        let args = self.collect_macro_args_from_slice(tokens, i + 2, end_j - 1);

        // Validate argument count
        if args.len() != macro_info.parameter_list.len() {
            // For conditional expressions, just skip problematic macro expansions
            return Ok(false);
        }

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            let _ = self.expand_tokens(&mut arg_clone, in_conditional);
            expanded_args.push(arg_clone);
        }

        let substituted = self.substitute_macro(&macro_info, &args, &expanded_args)?;
        let substituted = self.create_virtual_buffer_tokens(&substituted, symbol.as_str(), symbol_token.location);

        if substituted.len() > 10000 {
            return Ok(false);
        }

        tokens.splice(i..end_j, substituted);
        if let Some(m) = self.macros.get_mut(&symbol) {
            m.flags |= MacroFlags::USED;
        }

        Ok(true)
    }

    fn try_handle_pragma_operator(&mut self, tokens: &mut Vec<PPToken>, i: usize) -> bool {
        let token = tokens[i];
        if !matches!(token.kind, PPTokenKind::Identifier(s) if s.as_str() == "_Pragma") {
            return false;
        }

        // Need at least 3 more tokens: ( "string" )
        if i + 3 < tokens.len()
            && tokens[i + 1].kind == PPTokenKind::LeftParen
            && let PPTokenKind::StringLiteral(sym) = tokens[i + 2].kind
            && tokens[i + 3].kind == PPTokenKind::RightParen
        {
            let content = self.destringize(sym.as_str());
            self.perform_pragma(&content);
            tokens.drain(i..i + 4);
            return true;
        }
        false
    }

    /// Expand tokens by rescanning for further macro expansion
    fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>, in_conditional: bool) -> Result<(), PPError> {
        let mut i = 0;
        while i < tokens.len() {
            let token = tokens[i];

            if let Some(magic) = self.try_expand_magic_macro(&token) {
                tokens[i] = magic;
                i += 1;
                continue;
            }

            if in_conditional && let Some(new_i) = self.try_handle_conditional_operator(tokens, i)? {
                i = new_i;
                continue;
            }

            let PPTokenKind::Identifier(symbol) = token.kind else {
                i += 1;
                continue;
            };

            if self.is_recursive_expansion(token.location, symbol.as_str()) {
                i += 1;
                continue;
            }

            if self.try_expand_function_macro_in_tokens(tokens, i, in_conditional)? {
                continue;
            }

            if let Some(expanded) = self.expand_macro(&tokens[i])? {
                tokens.splice(i..i + 1, expanded);
                continue;
            }

            if self.try_handle_pragma_operator(tokens, i) {
                continue;
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

    fn is_recursive_expansion(&self, location: SourceLoc, macro_name: &str) -> bool {
        let expected_name = format!("<macro_{}>", macro_name);
        let expected_path = Path::new(&expected_name);

        std::iter::successors(self.sm.get_file_info(location.source_id()), |info| {
            info.include_loc.and_then(|loc| self.sm.get_file_info(loc.source_id()))
        })
        .take(100)
        .any(|info| info.path == expected_path)
    }

    fn create_virtual_buffer_tokens(
        &mut self,
        tokens: &[PPToken],
        macro_name: &str,
        trigger_location: SourceLoc,
    ) -> Vec<PPToken> {
        let virtual_id = self.sm.add_virtual_buffer(
            self.tokens_to_string(tokens).into_bytes(),
            &format!("macro_{}", macro_name),
            Some(trigger_location),
        );

        let mut offset = 0;
        tokens
            .iter()
            .map(|t| {
                let len = t.get_text().len() as u16;
                let is_pasted = self.sm.get_file_info(t.location.source_id()).is_some_and(|info| {
                    let p = info.path.to_string_lossy();
                    p == "<<pasted-tokens>>" || p == "<pasted-tokens>"
                });

                let loc = if is_pasted {
                    t.location
                } else {
                    SourceLoc::new(virtual_id, offset)
                };
                offset += len as u32;

                PPToken::new(t.kind, t.flags | PPTokenFlags::MACRO_EXPANDED, loc, len)
            })
            .collect()
    }

    /// Helper to report diagnostics
    fn report_diagnostic(
        &mut self,
        level: DiagnosticLevel,
        message: impl Into<String>,
        span: SourceSpan,
        code: Option<String>,
        hints: Vec<String>,
        related: Vec<SourceSpan>,
    ) {
        let diag = Diagnostic {
            level,
            message: message.into(),
            span,
            code,
            hints,
            related,
        };
        self.diag.report_diagnostic(diag);
    }

    /// Helper to report diagnostics with no related spans
    fn report_diagnostic_simple(
        &mut self,
        level: DiagnosticLevel,
        message: impl Into<String>,
        span: SourceSpan,
        code: Option<String>,
        hints: Vec<String>,
    ) {
        self.report_diagnostic(level, message, span, code, hints, Vec::new());
    }

    fn parse_macro_definition_params(
        &mut self,
        macro_name: &str,
    ) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
        let mut flags = MacroFlags::FUNCTION_LIKE;
        let mut params = Vec::new();
        let mut variadic = None;

        'param_parsing: loop {
            let param_token = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
            match param_token.kind {
                PPTokenKind::RightParen => break,
                PPTokenKind::Ellipsis => {
                    flags |= MacroFlags::C99_VARARGS;
                    variadic = Some(StringId::new("__VA_ARGS__"));
                    if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                        return Err(PPError::InvalidMacroParameter {
                            span: SourceSpan::new(param_token.location, param_token.location),
                        });
                    }
                    break;
                }
                PPTokenKind::Identifier(sym) => {
                    if params.contains(&sym) {
                        return Err(PPError::InvalidMacroParameter {
                            span: SourceSpan::new(param_token.location, param_token.location),
                        });
                    }
                    params.push(sym);

                    let sep = self.lex_token().ok_or(PPError::UnexpectedEndOfFile)?;
                    match sep.kind {
                        PPTokenKind::Comma => continue,
                        PPTokenKind::RightParen => break,
                        PPTokenKind::Ellipsis => {
                            variadic = Some(params.pop().unwrap());
                            flags |= MacroFlags::GNU_VARARGS;
                            if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                                return Err(PPError::InvalidMacroParameter {
                                    span: SourceSpan::new(sep.location, sep.location),
                                });
                            }
                            break;
                        }
                        _ => {
                            // Not a standard parameter list separator; treat as start of body.
                            // This pushes back both the separator and the identifier.
                            self.pending_tokens.push_front(sep);
                            self.pending_tokens.push_front(param_token);
                            break 'param_parsing;
                        }
                    }
                }
                _ => {
                    self.report_diagnostic(
                        DiagnosticLevel::Warning,
                        format!("Invalid macro parameter token in #define '{}'", macro_name),
                        SourceSpan::new(param_token.location, param_token.location),
                        Some("invalid_macro_parameter".to_string()),
                        vec!["Macro parameters must be identifiers".to_string()],
                        Vec::new(),
                    );

                    // Skip to the next divider
                    while let Some(t) = self.lex_token() {
                        if matches!(t.kind, PPTokenKind::Comma | PPTokenKind::RightParen) {
                            self.pending_tokens.push_front(t);
                            break;
                        }
                    }
                }
            }
        }

        Ok((flags, params, variadic))
    }
}
