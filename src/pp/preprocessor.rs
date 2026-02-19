use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::lang_options::CStandard;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use hashbrown::HashMap;
use std::borrow::Cow;
use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

use super::pp_lexer::PPLexer;
use crate::pp::interpreter::Interpreter;
use crate::pp::{HeaderSearch, PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::FileKind;
use std::path::{Path, PathBuf};
use target_lexicon::{Architecture, OperatingSystem, Triple};

/// Preprocessor directive kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Define,
    Undef,
    Include,
    IncludeNext,
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
    include_next: StringId,
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
    has_include_next: StringId,
    has_builtin: StringId,
    has_attribute: StringId,
    has_feature: StringId,
    has_extension: StringId,
    line_macro: StringId,
    file_macro: StringId,
    counter_macro: StringId,
    pragma_operator: StringId,
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
            include_next: StringId::new("include_next"),
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
            has_include_next: StringId::new("__has_include_next"),
            has_builtin: StringId::new("__has_builtin"),
            has_attribute: StringId::new("__has_attribute"),
            has_feature: StringId::new("__has_feature"),
            has_extension: StringId::new("__has_extension"),
            line_macro: StringId::new("__LINE__"),
            file_macro: StringId::new("__FILE__"),
            counter_macro: StringId::new("__COUNTER__"),
            pragma_operator: StringId::new("_Pragma"),
        }
    }

    fn is_directive(&self, symbol: StringId) -> Option<DirectiveKind> {
        if symbol == self.define {
            Some(DirectiveKind::Define)
        } else if symbol == self.undef {
            Some(DirectiveKind::Undef)
        } else if symbol == self.include {
            Some(DirectiveKind::Include)
        } else if symbol == self.include_next {
            Some(DirectiveKind::IncludeNext)
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

    /// Get the interned symbol for the "__has_include_next" operator
    pub(crate) fn has_include_next_symbol(&self) -> StringId {
        self.has_include_next
    }

    /// Get the interned symbol for the "__has_builtin" operator
    pub(crate) fn has_builtin_symbol(&self) -> StringId {
        self.has_builtin
    }

    /// Get the interned symbol for the "__has_attribute" operator
    pub(crate) fn has_attribute_symbol(&self) -> StringId {
        self.has_attribute
    }

    /// Get the interned symbol for the "__has_feature" operator
    pub(crate) fn has_feature_symbol(&self) -> StringId {
        self.has_feature
    }

    /// Get the interned symbol for the "__has_extension" operator
    pub(crate) fn has_extension_symbol(&self) -> StringId {
        self.has_extension
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
    pub(crate) tokens: Arc<[PPToken]>,
    pub(crate) parameter_list: Arc<[StringId]>,
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
    pub c_standard: CStandard,
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
            c_standard: CStandard::default(),
            target: Triple::host(),
            current_time: None,
        }
    }
}

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    sm: &'src mut SourceManager,
    diag: &'src mut DiagnosticEngine,
    c_standard: CStandard,
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
pub enum PPErrorKind {
    #[error("File not found: {path}")]
    FileNotFound { path: String },
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
    #[error("Invalid #line directive")]
    InvalidLineDirective,
    #[error("Multiple #else directives")]
    MultipleElse,
    #[error("#elif after #else")]
    ElifAfterElse,
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
    #[error("Unclosed preprocessor conditional directive")]
    UnclosedConditional,
    #[error("Invalid universal character name")]
    InvalidUniversalCharacterName,
}

#[derive(Debug)]
pub struct PPError {
    pub kind: PPErrorKind,
    pub span: SourceSpan,
}

impl std::fmt::Display for PPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::error::Error for PPError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.kind)
    }
}

impl From<PPError> for Diagnostic {
    fn from(val: PPError) -> Self {
        let level = DiagnosticLevel::Error;

        Diagnostic {
            level,
            message: val.kind.to_string(),
            span: val.span,
            ..Default::default()
        }
    }
}

impl crate::diagnostic::IntoDiagnostic for PPError {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        let span = self.span;
        let kind = self.kind;
        let mut diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message: kind.to_string(),
            span,
            ..Default::default()
        };

        // Add hints for certain error types
        match &kind {
            PPErrorKind::ElifWithoutIf => {
                diag.hints.push("perhaps you meant to use #if?".to_string());
            }
            PPErrorKind::ElseWithoutIf => {
                diag.hints
                    .push("perhaps you meant to use #ifdef or #ifndef?".to_string());
            }
            PPErrorKind::UnmatchedEndif => {
                diag.hints
                    .push("this #endif does not have a matching #if, #ifdef, or #ifndef".to_string());
            }
            PPErrorKind::MultipleElse => {
                diag.hints
                    .push("there can only be one #else directive per conditional level".to_string());
            }
            PPErrorKind::ElifAfterElse => {
                diag.hints
                    .push("#elif directives must come before the #else directive".to_string());
            }
            _ => {}
        }

        vec![diag]
    }
}

impl<'src> Preprocessor<'src> {
    /// Create a new preprocessor
    pub(crate) fn new(
        source_manager: &'src mut SourceManager,
        diag: &'src mut DiagnosticEngine,
        config: &PPConfig,
    ) -> Self {
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
        built_in_headers.insert("limits.h", include_str!("../../custom-include/limits.h"));

        let mut preprocessor = Preprocessor {
            sm: source_manager,
            diag,
            c_standard: config.c_standard,
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
        self.define_builtin_macro_string("__DATE__", &date_str);

        // __TIME__
        let time_str = format!("\"{:02}:{:02}:{:02}\"", now.hour(), now.minute(), now.second());
        self.define_builtin_macro_string("__TIME__", &time_str);

        // Other built-ins
        self.define_builtin_macro_one("__STDC__");

        // Target specific macros
        // Architecture
        match self.target.architecture {
            Architecture::X86_64 => {
                for macro_name in &["__x86_64__", "__x86_64", "__amd64__", "__amd64"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            Architecture::X86_32(_) => {
                for macro_name in &["__i386__", "__i386"] {
                    self.define_builtin_macro_one(macro_name);
                }
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
            for macro_name in &["__LP64__", "_LP64"] {
                self.define_builtin_macro_one(macro_name);
            }
        } else {
            for macro_name in &["__ILP32__", "_ILP32"] {
                self.define_builtin_macro_one(macro_name);
            }
        }

        // OS
        match self.target.operating_system {
            OperatingSystem::Linux => {
                for macro_name in &["__linux__", "__linux", "__unix__", "__unix", "__ELF__", "__gnu_linux__"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            OperatingSystem::Darwin(_) => {
                for macro_name in &["__APPLE__", "__MACH__"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            OperatingSystem::Windows => {
                self.define_builtin_macro_one("_WIN32");
                if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(32) == 64 {
                    self.define_builtin_macro_one("_WIN64");
                }
            }
            _ => {}
        }

        // GCC version macros for compatibility with glibc headers
        // We define these to match what Clang does for GCC compatibility
        self.define_builtin_macro("__extension__", vec![]);
        self.define_builtin_macro("__restrict", vec![]);
        self.define_builtin_macro_with_val("__GNUC__", "4");
        self.define_builtin_macro_with_val("__GNUC_MINOR__", "2");
        self.define_builtin_macro_with_val("__GNUC_PATCHLEVEL__", "1");

        if self.c_standard.is_c11() {
            self.define_builtin_macro_with_val("__STDC_VERSION__", "201112");
            self.define_builtin_macro_one("__STDC_HOSTED__");
            self.define_builtin_macro_one("__STDC_MB_MIGHT_NEQ_WC__");
            self.define_builtin_macro_one("__STDC_IEC_559__");
            self.define_builtin_macro_one("__STDC_IEC_559_COMPLEX__");
            self.define_builtin_macro_with_val("__STDC_ISO_10646__", "201103L");
            self.define_builtin_macro_one("__STDC_UTF_16__");
            self.define_builtin_macro_one("__STDC_UTF_32__");
        }
    }

    /// Helper to define a built-in macro with value "1"
    fn define_builtin_macro_one(&mut self, name: &str) {
        self.define_builtin_macro_with_val(name, "1");
    }

    /// Helper to define a built-in macro with a specific number value
    fn define_builtin_macro_with_val(&mut self, name: &str, value: &str) {
        self.define_builtin_macro(
            name,
            vec![PPToken::new(
                PPTokenKind::Number(StringId::new(value)),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                value.len() as u16,
            )],
        );
    }

    /// Helper to define a built-in macro with a string value
    fn define_builtin_macro_string(&mut self, name: &str, value: &str) {
        self.define_builtin_macro(
            name,
            vec![PPToken::new(
                PPTokenKind::StringLiteral(StringId::new(value)),
                PPTokenFlags::empty(),
                SourceLoc::builtin(),
                value.len() as u16,
            )],
        );
    }

    /// Define a macro from command line or other external source
    pub(crate) fn define_user_macro(&mut self, name: &str, value: Option<&str>) {
        let value_str = value.unwrap_or("1");

        // Create a buffer for the macro value
        let source_id = self
            .sm
            .add_buffer(value_str.as_bytes().to_vec(), "<command-line>", None);
        let buffer = self.sm.get_buffer_arc(source_id);
        let mut lexer = PPLexer::new(source_id, buffer);

        let mut tokens = Vec::new();
        while let Some(token) = lexer.next_token() {
            if matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
                continue;
            }
            tokens.push(token);
        }

        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::builtin(),
            flags: MacroFlags::empty(), // Not BUILTIN, so it can be redefined (with warning if different)
            tokens: Arc::from(tokens),
            parameter_list: Arc::from([]),
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Define a built-in macro
    fn define_builtin_macro(&mut self, name: &str, tokens: Vec<PPToken>) {
        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::builtin(),
            flags: MacroFlags::BUILTIN,
            tokens: Arc::from(tokens),
            parameter_list: Arc::from([]),
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
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

    /// Get the interned symbol for the "__has_include_next" operator
    pub(crate) fn has_include_next_symbol(&self) -> StringId {
        self.directive_keywords.has_include_next_symbol()
    }

    /// Get the interned symbol for the "__has_builtin" operator
    pub(crate) fn has_builtin_symbol(&self) -> StringId {
        self.directive_keywords.has_builtin_symbol()
    }

    /// Get the interned symbol for the "__has_attribute" operator
    pub(crate) fn has_attribute_symbol(&self) -> StringId {
        self.directive_keywords.has_attribute_symbol()
    }

    /// Get the interned symbol for the "__has_feature" operator
    pub(crate) fn has_feature_symbol(&self) -> StringId {
        self.directive_keywords.has_feature_symbol()
    }

    /// Get the interned symbol for the "__has_extension" operator
    pub(crate) fn has_extension_symbol(&self) -> StringId {
        self.directive_keywords.has_extension_symbol()
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

    /// Check if a header exists for #include_next
    pub(crate) fn check_next_header_exists(&self, path: &str, is_angled: bool) -> bool {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        self.header_search
            .resolve_next_path(path, is_angled, current_dir)
            .is_some()
    }

    /// Expect and consume an Eod token or end of file
    fn expect_eod(&mut self) -> Result<(), PPError> {
        match self.lex_token() {
            Some(token) if token.kind == PPTokenKind::Eod => Ok(()),
            None => Ok(()), // End of file is acceptable
            Some(token) => self.emit_error_loc(PPErrorKind::ExpectedEod, token.location),
        }
    }

    /// Expect a token, and fail with UnexpectedEndOfFile if None is returned
    fn expect_token(&mut self) -> Result<PPToken, PPError> {
        self.lex_token()
            .ok_or_else(|| self.error(PPErrorKind::UnexpectedEndOfFile, self.get_current_span()))
    }

    /// Expect a token of a specific kind
    fn expect_kind(&mut self, kind: PPTokenKind) -> Result<PPToken, PPError> {
        let token = self.expect_token()?;
        if token.kind == kind {
            Ok(token)
        } else {
            self.emit_error_loc(PPErrorKind::InvalidDirective, token.location)
        }
    }

    /// Expect a string literal token
    fn expect_string_literal(&mut self) -> Result<(StringId, SourceLoc), PPError> {
        let token = self.expect_token()?;
        if let PPTokenKind::StringLiteral(s) = token.kind {
            Ok((s, token.location))
        } else {
            self.emit_error_loc(PPErrorKind::InvalidDirective, token.location)
        }
    }

    /// Expect an identifier token
    fn expect_identifier(&mut self) -> Result<(PPToken, StringId), PPError> {
        let token = self.expect_token()?;
        if let PPTokenKind::Identifier(sym) = token.kind {
            Ok((token, sym))
        } else {
            self.emit_error_loc(PPErrorKind::ExpectedIdentifier, token.location)
        }
    }

    /// Collect tokens balanced between open and close delimiters.
    /// Assumes the opening delimiter has NOT been consumed yet and will consume it.
    fn collect_balanced_tokens(&mut self, open: PPTokenKind, close: PPTokenKind) -> Result<Vec<PPToken>, PPError> {
        self.expect_kind(open)?;
        // ⚡ Bolt: Use a small initial capacity to avoid reallocations for common short expressions.
        let mut tokens = Vec::with_capacity(8);
        let mut depth = 1;
        while let Some(t) = self.lex_token() {
            if t.kind == PPTokenKind::Eod {
                return self.emit_error_loc(PPErrorKind::UnexpectedEndOfFile, t.location);
            }
            if t.kind == open {
                depth += 1;
            } else if t.kind == close {
                depth -= 1;
                if depth == 0 {
                    return Ok(tokens);
                }
            }
            tokens.push(t);
        }
        self.emit_error_loc(PPErrorKind::UnexpectedEndOfFile, self.get_current_location())
    }

    /// Helper to extract content of a string literal, stripping quotes.
    fn extract_string_literal_content(
        &self,
        symbol: StringId,
        location: SourceLoc,
        error_kind: PPErrorKind,
    ) -> Result<String, PPError> {
        let s = symbol.as_str();
        s.strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .map(|s| s.to_string())
            .ok_or_else(|| self.error_loc(error_kind, location))
    }

    /// Process source file and return preprocessed tokens
    pub(crate) fn process(&mut self, source_id: SourceId, _config: &PPConfig) -> Result<Vec<PPToken>, PPError> {
        // Initialize lexer for main file
        let buffer_len = self.sm.get_buffer(source_id).len() as u32;
        let buffer = self.sm.get_buffer_arc(source_id);

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
                    if let Some(magic) = self.try_expand_magic_macro(&token) {
                        result_tokens.push(magic);
                    } else if symbol == self.directive_keywords.pragma_operator {
                        self.handle_pragma_operator()?;
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
            return self.emit_error_loc(PPErrorKind::UnclosedConditional, loc);
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

    fn get_current_span(&self) -> SourceSpan {
        let loc = self.get_current_location();
        SourceSpan::new(loc, loc)
    }

    fn error(&self, kind: PPErrorKind, span: SourceSpan) -> PPError {
        PPError { kind, span }
    }

    fn error_loc(&self, kind: PPErrorKind, loc: SourceLoc) -> PPError {
        PPError {
            kind,
            span: SourceSpan::new(loc, loc),
        }
    }

    fn emit_error<T>(&self, kind: PPErrorKind, span: SourceSpan) -> Result<T, PPError> {
        Err(PPError { kind, span })
    }

    fn emit_error_loc<T>(&self, kind: PPErrorKind, loc: SourceLoc) -> Result<T, PPError> {
        Err(PPError {
            kind,
            span: SourceSpan::new(loc, loc),
        })
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
            let loc = self.get_current_location();
            return self.emit_error_loc(PPErrorKind::InvalidConditionalExpression, loc);
        }

        Ok(tokens)
    }

    /// Evaluate a conditional expression (simplified - handle defined and basic arithmetic)
    fn evaluate_conditional_expression(&mut self, tokens: Vec<PPToken>) -> Result<bool, PPError> {
        // Bolt ⚡: Removed redundant filtering of Eod tokens and a buggy optimization.
        // parse_conditional_expression already ensures no Eod tokens are present.
        // This avoids two allocations and two full clones of the token list.
        // The buggy 'defined' optimization was also removed as it incorrectly
        // returned early for complex expressions like '#if defined(FOO) && 0'.
        // Bolt ⚡: Optimized to take tokens by value, avoiding a redundant `to_vec()` clone.
        if tokens.is_empty() {
            // For empty expressions, treat as false
            return Ok(false);
        }

        // First, expand macros in the expression
        let mut expanded_tokens = tokens;
        match self.expand_tokens(&mut expanded_tokens, true) {
            Ok(_) => {}
            Err(_e) => {
                // If macro expansion fails, emit diagnostic and treat as false
                self.report_warning(
                    "Failed to expand macros in conditional expression",
                    self.get_current_location(),
                );
                return Ok(false);
            }
        }

        self.evaluate_arithmetic_expression(&expanded_tokens)
    }

    /// Evaluate a simple arithmetic expression for #if/#elif
    fn evaluate_arithmetic_expression(&mut self, tokens: &[PPToken]) -> Result<bool, PPError> {
        if tokens.is_empty() {
            let loc = self.get_current_location();
            return self.emit_error_loc(PPErrorKind::InvalidConditionalExpression, loc);
        }

        let mut interpreter = Interpreter::new(tokens, self);
        let result = interpreter.evaluate();

        match result {
            Ok(val) => Ok(val.is_truthy()),
            Err(_) => {
                // For complex expressions that can't be parsed, emit a warning and treat as false
                self.report_warning(
                    "Invalid conditional expression in preprocessor directive",
                    self.get_current_location(),
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
                        let err = self.error_loc(PPErrorKind::InvalidUniversalCharacterName, token.location);
                        self.report_pp_error(err);
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
        let token = self.expect_token()?;

        match token.kind {
            PPTokenKind::Identifier(sym) => match self.directive_keywords.is_directive(sym) {
                Some(kind) => match kind {
                    DirectiveKind::If
                    | DirectiveKind::Ifdef
                    | DirectiveKind::Ifndef
                    | DirectiveKind::Elif
                    | DirectiveKind::Else
                    | DirectiveKind::Endif => self.handle_conditional_directive(kind, token.location),
                    _ => {
                        if self.is_currently_skipping() {
                            self.skip_directive()
                        } else {
                            self.execute_directive(kind)
                        }
                    }
                },
                None => self.emit_error_loc(PPErrorKind::InvalidDirective, token.location),
            },
            PPTokenKind::Eod => Ok(()),
            _ => self.emit_error_loc(PPErrorKind::InvalidDirective, token.location),
        }
    }

    fn handle_conditional_directive(&mut self, kind: DirectiveKind, location: SourceLoc) -> Result<(), PPError> {
        match kind {
            DirectiveKind::If | DirectiveKind::Ifdef | DirectiveKind::Ifndef => {
                if self.is_currently_skipping() {
                    self.push_skipped_conditional();
                    self.skip_directive()
                } else {
                    match kind {
                        DirectiveKind::If => {
                            let tokens = self.parse_conditional_expression().unwrap_or_default();
                            let cond = self.evaluate_conditional_expression(tokens).unwrap_or(false);
                            self.handle_if_directive(cond)
                        }
                        DirectiveKind::Ifdef => self.handle_ifdef(),
                        DirectiveKind::Ifndef => self.handle_ifndef(),
                        _ => unreachable!(),
                    }
                }
            }
            DirectiveKind::Elif => {
                if self.should_evaluate_conditional() {
                    let tokens = self.parse_conditional_expression().unwrap_or_default();
                    let cond = self.evaluate_conditional_expression(tokens).unwrap_or(false);
                    self.handle_elif_directive(cond, location)
                } else {
                    self.handle_elif_directive(false, location)
                }
            }
            DirectiveKind::Else => self.handle_else(location),
            DirectiveKind::Endif => self.handle_endif(location),
            _ => unreachable!(),
        }
    }

    fn execute_directive(&mut self, kind: DirectiveKind) -> Result<(), PPError> {
        match kind {
            DirectiveKind::Define => self.handle_define(),
            DirectiveKind::Undef => self.handle_undef(),
            DirectiveKind::Include => self.handle_include(),
            DirectiveKind::IncludeNext => self.handle_include_next(),
            DirectiveKind::Line => self.handle_line(),
            DirectiveKind::Pragma => self.handle_pragma(),
            DirectiveKind::Error => self.handle_error(),
            DirectiveKind::Warning => self.handle_warning(),
            _ => unreachable!("Conditional directives handled separately"),
        }
    }

    /// Handle _Pragma("...") operator
    fn handle_pragma_operator(&mut self) -> Result<(), PPError> {
        // We have already consumed the `_Pragma` identifier.
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (symbol, _) = self.expect_string_literal()?;
        let pragma_content = self.destringize(symbol.as_str());
        self.expect_kind(PPTokenKind::RightParen)?;

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
        let buffer = self.sm.get_buffer_arc(source_id);
        let mut temp_lexer = PPLexer::new(source_id, buffer);

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
            let first_param = self.expect_token()?;

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
                self.report_warning(
                    format!("Redefinition of built-in macro '{}'", name),
                    name_token.location,
                );
                return false;
            }

            // Check if definition is different
            // Mask out runtime state flags (USED, DISABLED) that don't affect definition identity
            let definition_flags_mask =
                MacroFlags::FUNCTION_LIKE | MacroFlags::C99_VARARGS | MacroFlags::GNU_VARARGS | MacroFlags::BUILTIN;
            let is_different = (existing.flags & definition_flags_mask) != (macro_info.flags & definition_flags_mask)
                || existing.parameter_list != macro_info.parameter_list
                || existing.variadic_arg != macro_info.variadic_arg
                || existing.tokens.len() != macro_info.tokens.len()
                || existing
                    .tokens
                    .iter()
                    .zip(macro_info.tokens.iter())
                    .any(|(a, b)| a.kind != b.kind);

            if is_different {
                self.report_warning(
                    format!("Redefinition of macro '{}'", name.as_str()),
                    name_token.location,
                );
            }
        }
        true
    }

    fn handle_define(&mut self) -> Result<(), PPError> {
        let (name_token, name) = self.expect_identifier()?;

        let (flags, params, variadic) = self.parse_define_args(name.as_str())?;

        // Collect body tokens
        // Use collect_tokens_until_eod which handles the loop and checking for Eod
        let tokens = self.collect_tokens_until_eod();

        // Store the macro
        let macro_info = MacroInfo {
            location: name_token.location,
            flags,
            tokens: Arc::from(tokens),
            parameter_list: Arc::from(params),
            variadic_arg: variadic,
        };

        if self.check_macro_redefinition(name, &name_token, &macro_info) {
            self.macros.insert(name, macro_info);
        }
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPError> {
        let (name_token, name) = self.expect_identifier()?;

        if let Some(existing) = self.macros.get(&name)
            && existing.flags.contains(MacroFlags::BUILTIN)
        {
            self.report_warning(
                format!("Undefining built-in macro '{}'", name.as_str()),
                name_token.location,
            );
            self.expect_eod()?;
            return Ok(());
        }

        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn do_handle_include(&mut self, is_next: bool) -> Result<(), PPError> {
        let token = self.expect_token()?;
        let mut eod_consumed = false;

        let (path_str, is_angled) = match token.kind {
            PPTokenKind::StringLiteral(symbol) => {
                let path =
                    self.extract_string_literal_content(symbol, token.location, PPErrorKind::InvalidIncludePath)?;
                (path, false)
            }
            PPTokenKind::Less => {
                let mut path_parts = Vec::new();
                while let Some(t) = self.lex_token() {
                    if t.kind == PPTokenKind::Greater {
                        break;
                    }
                    path_parts.push(t);
                }
                (self.tokens_to_string(&path_parts), true)
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
                    return self.emit_error_loc(PPErrorKind::InvalidIncludePath, token.location);
                }

                let first = &tokens[0];
                match first.kind {
                    PPTokenKind::StringLiteral(symbol) => {
                        if tokens.len() > 1 {
                            return self.emit_error_loc(PPErrorKind::ExpectedEod, tokens[1].location);
                        }
                        let path = self.extract_string_literal_content(
                            symbol,
                            first.location,
                            PPErrorKind::InvalidIncludePath,
                        )?;
                        (path, false)
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
                        let idx = greater_idx
                            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidIncludePath, token.location))?;
                        if idx + 1 < tokens.len() {
                            return self.emit_error_loc(PPErrorKind::ExpectedEod, tokens[idx + 1].location);
                        }
                        (self.tokens_to_string(&path_parts), true)
                    }
                    _ => {
                        return self.emit_error_loc(PPErrorKind::InvalidIncludePath, token.location);
                    }
                }
            }
        };

        if self.include_depth >= self.max_include_depth {
            return self.emit_error_loc(PPErrorKind::IncludeDepthExceeded, token.location);
        }

        let include_source_id = if is_next {
            self.resolve_next_include_path(&path_str, is_angled, token.location)?
        } else {
            self.resolve_include_path(&path_str, is_angled, token.location)?
        };

        if self.once_included.contains(&include_source_id) {
            return Ok(());
        }

        self.include_stack.push(IncludeStackInfo {
            file_id: include_source_id,
        });

        if !eod_consumed {
            self.expect_eod()?;
        }

        let buffer = self.sm.get_buffer_arc(include_source_id);
        self.lexer_stack.push(PPLexer::new(include_source_id, buffer));
        self.include_depth += 1;

        Ok(())
    }

    fn handle_include(&mut self) -> Result<(), PPError> {
        self.do_handle_include(false)
    }

    fn handle_include_next(&mut self) -> Result<(), PPError> {
        self.do_handle_include(true)
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
            return self
                .sm
                .add_file_from_path(&path_buf, Some(loc))
                .map_err(|_| self.error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc));
        }

        let fallback_id = if is_angled {
            self.built_in_file_ids.get(path).copied()
        } else {
            self.sm.get_file_id(path)
        };

        if let Some(id) = fallback_id {
            Ok(id)
        } else {
            self.emit_error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
        }
    }

    fn resolve_next_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPError> {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        let resolved = self.header_search.resolve_next_path(path, is_angled, current_dir);

        if let Some(path_buf) = resolved {
            return self
                .sm
                .add_file_from_path(&path_buf, Some(loc))
                .map_err(|_| self.error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc));
        }

        if is_angled && let Some(id) = self.built_in_file_ids.get(path).copied() {
            let is_recursive = if let Some(current) = self.lexer_stack.last() {
                current.source_id == id
            } else {
                false
            };

            if !is_recursive {
                return Ok(id);
            }
        }

        self.emit_error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
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
        let (_, sym) = self.expect_identifier()?;

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
            return self.emit_error_loc(PPErrorKind::ElifWithoutIf, location);
        }
        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            return self.emit_error_loc(PPErrorKind::ElifAfterElse, location);
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
            return self.emit_error_loc(PPErrorKind::ElseWithoutIf, location);
        }
        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            return self.emit_error_loc(PPErrorKind::MultipleElse, location);
        }

        current.found_else = true;
        let should_process = !current.found_non_skipping;
        current.was_skipping = !should_process;

        self.expect_eod()
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.pop().is_none() {
            return self.emit_error_loc(PPErrorKind::UnmatchedEndif, location);
        }
        self.expect_eod()
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
        let (first, rest) = tokens
            .split_first()
            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidLineDirective, SourceLoc::builtin()))?;

        let PPTokenKind::Number(symbol) = first.kind else {
            return self.emit_error_loc(PPErrorKind::InvalidLineDirective, first.location);
        };

        let line_num = symbol
            .as_str()
            .parse::<u32>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidLineDirective, first.location))?;

        let filename = match rest {
            [] => None,
            [t] => {
                let PPTokenKind::StringLiteral(s) = t.kind else {
                    return self.emit_error_loc(PPErrorKind::InvalidLineDirective, t.location);
                };
                Some(self.extract_string_literal_content(s, t.location, PPErrorKind::InvalidLineDirective)?)
            }
            _ => return self.emit_error_loc(PPErrorKind::InvalidLineDirective, first.location),
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
            let loc = self.get_current_location();
            return self.emit_error_loc(PPErrorKind::InvalidLineDirective, loc);
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
        let (token, symbol) = self.expect_identifier()?;

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
                return self.emit_error_loc(PPErrorKind::UnknownPragma(pragma_name.to_string()), token.location);
            }
        }

        self.collect_tokens_until_eod();
        Ok(())
    }

    fn parse_pragma_macro_name(&mut self) -> Result<StringId, PPError> {
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (symbol, token_loc) = self.expect_string_literal()?;

        let name = self.extract_string_literal_content(symbol, token_loc, PPErrorKind::InvalidDirective)?;

        self.expect_kind(PPTokenKind::RightParen)?;

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
        let mut tokens = self.collect_balanced_tokens(PPTokenKind::LeftParen, PPTokenKind::RightParen)?;
        self.expand_tokens(&mut tokens, false)?;

        tokens.into_iter().try_fold(String::new(), |mut acc, t| {
            let PPTokenKind::StringLiteral(symbol) = t.kind else {
                return self.emit_error_loc(PPErrorKind::InvalidDirective, t.location);
            };
            acc.push_str(&self.destringize(symbol.as_str()));
            Ok(acc)
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
            self.emit_error_loc(PPErrorKind::PragmaError(message), loc)
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

    fn handle_diagnostic_directive(&mut self, is_error: bool) -> Result<(), PPError> {
        let directive_location = self.get_current_location();
        let message = self.read_directive_message();

        let formatted_message = if is_error {
            format!("#error directive: {}", message)
        } else {
            message.clone()
        };

        if is_error {
            self.report_error(formatted_message, directive_location);
        } else {
            self.report_warning(formatted_message, directive_location);
        }

        if is_error {
            self.emit_error_loc(PPErrorKind::ErrorDirective(message), directive_location)
        } else {
            Ok(())
        }
    }

    fn handle_error(&mut self) -> Result<(), PPError> {
        self.handle_diagnostic_directive(true)
    }

    fn handle_warning(&mut self) -> Result<(), PPError> {
        self.handle_diagnostic_directive(false)
    }

    fn read_directive_message(&mut self) -> String {
        let tokens = self.collect_tokens_until_eod();
        self.tokens_to_string(&tokens)
    }

    /// Expand a macro if it exists
    fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPError> {
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

        // Bolt ⚡: Check for recursive expansion here to avoid walking include stack for non-macros.
        if self.is_recursive_expansion(token.location, symbol.as_str()) {
            return Ok(None);
        }

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
        // Bolt ⚡: Optimized two-pass string building.
        // We use the token's length field for the first pass as it's a fast u16 access.
        let total_len: usize = tokens.iter().map(|t| t.length as usize).sum();

        let mut result = String::with_capacity(total_len);
        let mut cache = SourceBufferCache::new(self.sm);

        for token in tokens {
            result.push_str(cache.get_token_text(token));
        }
        result
    }

    /// Helper to create a virtual buffer and expand tokens within it
    fn expand_virtual_buffer(
        &mut self,
        tokens: &[PPToken],
        name: &str,
        location: SourceLoc,
    ) -> Result<Vec<PPToken>, PPError> {
        // For Level B: Create a virtual buffer containing the replacement text
        let mut expanded = self.create_virtual_buffer_tokens(tokens, name, location);

        // Recursively expand any macros in the replacement
        self.expand_tokens(&mut expanded, false)?;

        Ok(expanded)
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        self.expand_virtual_buffer(&macro_info.tokens, symbol.as_str(), token.location)
    }

    /// Expand a function-like macro
    fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        // Parse arguments from lexer
        let args = match self.parse_macro_args_from_lexer(macro_info) {
            Ok(args) => args,
            Err(PPError {
                kind: PPErrorKind::InvalidMacroParameter,
                ..
            }) => {
                return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, token.location);
            }
            Err(e) => return Err(e),
        };

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            self.expand_tokens(&mut arg_clone, false)?;
            expanded_args.push(arg_clone);
        }

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args, &expanded_args)?;

        self.expand_virtual_buffer(&substituted, symbol.as_str(), token.location)
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(&mut self, macro_info: &MacroInfo) -> Result<Vec<Vec<PPToken>>, PPError> {
        let token = self.expect_token()?;
        if token.kind != PPTokenKind::LeftParen {
            self.pending_tokens.push_front(token);
            return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, token.location);
        }

        let mut args = Vec::with_capacity(macro_info.parameter_list.len());
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

                    return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, macro_info.location);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(t),
            }
        }

        self.emit_error(PPErrorKind::UnexpectedEndOfFile, self.get_current_span())
    }

    /// Helper to collect variadic arguments with commas inserted
    fn collect_variadic_args_with_commas(
        &mut self,
        args: &[Vec<PPToken>],
        start_index: usize,
        trigger_loc: SourceLoc,
    ) -> Vec<PPToken> {
        // ⚡ Bolt: Pre-allocate result vector and avoid redundant clones.
        let mut total_tokens = 0;
        let num_args = args.len().saturating_sub(start_index);
        if num_args > 0 {
            total_tokens += num_args - 1; // for commas
            for arg in args.iter().skip(start_index) {
                total_tokens += arg.len();
            }
        }
        let mut result = Vec::with_capacity(total_tokens);

        let mut first = true;

        // We need a source for the comma token.
        // We create a virtual buffer for it to ensure stringification works correctly.
        // We only create it if we actually need a comma.
        let comma_source_id = if num_args > 1 {
            Some(
                self.sm
                    .add_virtual_buffer(b",".to_vec(), "<comma>", Some(trigger_loc), FileKind::Virtual),
            )
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
            result.extend_from_slice(arg);
            first = false;
        }
        result
    }

    fn is_macro_param(&self, macro_info: &MacroInfo, symbol: StringId) -> bool {
        macro_info.variadic_arg == Some(symbol) || macro_info.parameter_list.contains(&symbol)
    }

    fn get_macro_param_tokens<'a>(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        args: &'a [Vec<PPToken>],
        location: SourceLoc,
    ) -> Option<Cow<'a, [PPToken]>> {
        if let Some(idx) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
            return Some(Cow::Borrowed(&args[idx]));
        }
        if macro_info.variadic_arg == Some(symbol) {
            let start = macro_info.parameter_list.len();
            return Some(Cow::Owned(
                self.collect_variadic_args_with_commas(args, start, location),
            ));
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
        // Bolt ⚡: Pre-allocate result vector to minimize reallocations during substitution.
        let mut result = Vec::with_capacity(macro_info.tokens.len());
        let mut i = 0;
        let mut last_token_produced_output = false;

        while i < macro_info.tokens.len() {
            let token = &macro_info.tokens[i];

            match token.kind {
                PPTokenKind::Hash if i + 1 < macro_info.tokens.len() => {
                    let next = &macro_info.tokens[i + 1];
                    if let PPTokenKind::Identifier(sym) = next.kind
                        && let Some(arg) = self.get_macro_param_tokens(macro_info, sym, args, token.location)
                    {
                        let stringified = self.stringify_tokens(&arg, token.location)?;
                        result.push(stringified);
                        last_token_produced_output = true;
                        i += 2;
                        continue;
                    }
                }
                PPTokenKind::HashHash if i + 1 < macro_info.tokens.len() => {
                    let right_token = &macro_info.tokens[i + 1];
                    let left = if last_token_produced_output { result.pop() } else { None };

                    let (pasted, produced_output) = self.perform_token_pasting(macro_info, left, right_token, args)?;

                    result.extend(pasted);
                    last_token_produced_output = produced_output;
                    i += 2;
                    continue;
                }
                PPTokenKind::Identifier(sym) if self.is_macro_param(macro_info, sym) => {
                    let next_is_hh =
                        i + 1 < macro_info.tokens.len() && macro_info.tokens[i + 1].kind == PPTokenKind::HashHash;
                    let src = if next_is_hh { args } else { expanded_args };
                    if let Some(param_tokens) = self.get_macro_param_tokens(macro_info, sym, src, token.location) {
                        if param_tokens.is_empty() {
                            last_token_produced_output = false;
                        } else {
                            result.extend(param_tokens.iter().copied());
                            last_token_produced_output = true;
                        }
                    } else {
                        last_token_produced_output = false;
                    }
                }
                _ => {
                    result.push(*token);
                    last_token_produced_output = true;
                }
            }
            i += 1;
        }

        Ok(result)
    }

    /// Perform token pasting logic for the ## operator, including GNU comma swallowing.
    fn perform_token_pasting(
        &mut self,
        macro_info: &MacroInfo,
        left: Option<PPToken>,
        right_token: &PPToken,
        args: &[Vec<PPToken>],
    ) -> Result<(Vec<PPToken>, bool), PPError> {
        let right_tokens = if let PPTokenKind::Identifier(sym) = right_token.kind {
            self.get_macro_param_tokens(macro_info, sym, args, right_token.location)
                .unwrap_or(Cow::Borrowed(std::slice::from_ref(right_token)))
        } else {
            Cow::Borrowed(std::slice::from_ref(right_token))
        };

        if right_tokens.is_empty() {
            // Right operand is empty (placemarker).
            let is_comma = left.as_ref().is_some_and(|t| t.kind == PPTokenKind::Comma);
            let is_variadic =
                matches!(right_token.kind, PPTokenKind::Identifier(s) if macro_info.variadic_arg == Some(s));

            if is_comma && is_variadic {
                // GNU Comma Swallowing extension: swallow the comma.
                Ok((Vec::new(), false))
            } else if let Some(l) = left {
                // Standard behavior: paste left with empty -> left.
                Ok((vec![l], true))
            } else {
                Ok((Vec::new(), false))
            }
        } else if let Some(l) = left {
            // Right is not empty, Left is not empty: paste left with right[0].
            let mut pasted = self.paste_tokens(&l, &right_tokens[0])?;
            let pasted_count = pasted.len();
            pasted.extend(right_tokens.iter().skip(1).copied());
            Ok((pasted, pasted_count > 0 || right_tokens.len() > 1))
        } else {
            // Right is not empty, Left is empty: empty ## right -> right.
            Ok((right_tokens.into_owned(), true))
        }
    }

    /// Stringify tokens for # operator
    pub(crate) fn stringify_tokens(&self, tokens: &[PPToken], location: SourceLoc) -> Result<PPToken, PPError> {
        // Bolt ⚡: Use a two-pass approach to build the stringified token efficiently.
        let mut total_len = 2; // For the opening and closing quotes
        let mut cache = SourceBufferCache::new(self.sm);

        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                total_len += 1;
            }
            let bytes = cache.get_token_bytes(token);
            for &b in bytes {
                match b {
                    b'"' | b'\\' => total_len += 2,
                    _ => total_len += 1,
                }
            }
        }

        let mut result = String::with_capacity(total_len);
        result.push('"');

        cache.reset();
        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(' ');
            }

            let bytes = cache.get_token_bytes(token);
            let mut last_start = 0;
            for (j, &b) in bytes.iter().enumerate() {
                if b == b'"' || b == b'\\' {
                    if j > last_start {
                        result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..j]) });
                    }
                    result.push('\\');
                    result.push(b as char);
                    last_start = j + 1;
                }
            }
            if last_start < bytes.len() {
                result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..]) });
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
            return self.emit_error_loc(PPErrorKind::InvalidTokenPasting, left.location);
        };

        let right_buffer = self.sm.get_buffer(right.location.source_id());
        let right_start = right.location.offset() as usize;
        let right_end = right_start + right.length as usize;
        let right_text = if right_end <= right_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&right_buffer[right_start..right_end]) }
        } else {
            return self.emit_error_loc(PPErrorKind::InvalidTokenPasting, right.location);
        };

        // ⚡ Bolt: Avoid redundant format! and clone by building the byte buffer directly.
        let mut virtual_buffer = Vec::with_capacity(left_text.len() + right_text.len());
        virtual_buffer.extend_from_slice(left_text.as_bytes());
        virtual_buffer.extend_from_slice(right_text.as_bytes());
        let virtual_id = self
            .sm
            .add_virtual_buffer(virtual_buffer, "pasted-tokens", None, FileKind::PastedToken);

        // Create a temporary lexer to lex the pasted text
        let buffer = self.sm.get_buffer_arc(virtual_id);
        let mut lexer = PPLexer::new(virtual_id, buffer);

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
        if !current_arg.is_empty() || !args.is_empty() {
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
        let PPTokenKind::Identifier(sym) = tokens[i].kind else {
            return Ok(None);
        };

        if sym == self.directive_keywords.defined {
            let next = i + 1;
            let end = match tokens.get(next).map(|t| &t.kind) {
                Some(PPTokenKind::LeftParen) => self.find_balanced_paren_range(tokens, next).unwrap_or(next),
                _ => next + 1,
            };
            return Ok(Some(end.min(tokens.len())));
        }
        if sym == self.directive_keywords.has_include || sym == self.directive_keywords.has_include_next {
            let next = i + 1;
            if let Some(PPTokenKind::LeftParen) = tokens.get(next).map(|t| &t.kind) {
                let arg_start = next + 1;
                if let Some(arg_t) = tokens.get(arg_start)
                    && let Some(arg_end) = self.find_balanced_paren_range(tokens, next)
                {
                    match arg_t.kind {
                        PPTokenKind::Less | PPTokenKind::StringLiteral(_) => {
                            return Ok(Some(arg_end));
                        }
                        _ => {
                            // Computed form: __has_include(MACRO)
                            let mut args = tokens[arg_start..arg_end - 1].to_vec();
                            self.expand_has_include_computed_args(&mut args);
                            let len = args.len();
                            tokens.splice(arg_start..arg_end - 1, args);
                            return Ok(Some(arg_start + len + 1));
                        }
                    }
                }
            }
            return Ok(Some(next.min(tokens.len())));
        }

        if sym == self.directive_keywords.has_builtin
            || sym == self.directive_keywords.has_attribute
            || sym == self.directive_keywords.has_feature
            || sym == self.directive_keywords.has_extension
        {
            let next = i + 1;
            let arg_end = tokens
                .get(next)
                .filter(|t| t.kind == PPTokenKind::LeftParen)
                .and_then(|_| self.find_balanced_paren_range(tokens, next));

            if let Some(arg_end) = arg_end {
                // Argument to __has_builtin and friends should be expanded if it's a macro.
                let arg_start = next + 1;
                let mut args = tokens[arg_start..arg_end - 1].to_vec();
                self.expand_tokens(&mut args, false)?;
                let len = args.len();
                tokens.splice(arg_start..arg_end - 1, args);
                return Ok(Some(arg_start + len + 1));
            }
            return Ok(Some(next.min(tokens.len())));
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

        // Bolt ⚡: Check for recursive expansion here to avoid walking include stack for non-macros.
        if self.is_recursive_expansion(symbol_token.location, symbol.as_str()) {
            return Ok(false);
        }

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
        if !matches!(token.kind, PPTokenKind::Identifier(s) if s == self.directive_keywords.pragma_operator) {
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

            if !matches!(token.kind, PPTokenKind::Identifier(_)) {
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
        // Bolt ⚡: Optimization: avoid format! and Path allocation in a hot loop.
        // We check the path directly by string prefix/suffix which is much faster.
        std::iter::successors(self.sm.get_file_info(location.source_id()), |info| {
            info.include_loc.and_then(|loc| self.sm.get_file_info(loc.source_id()))
        })
        .take(100)
        .any(|info| {
            let path_str = info.path.to_str().unwrap_or("");
            // Bolt ⚡: Prefix "<macro_" is 7 chars, suffix ">" is 1 char. Total 8.
            path_str.len() == macro_name.len() + 8
                && path_str.starts_with("<macro_")
                && path_str.ends_with('>')
                && &path_str[7..path_str.len() - 1] == macro_name
        })
    }

    fn create_virtual_buffer_tokens(
        &mut self,
        tokens: &[PPToken],
        macro_name: &str,
        trigger_location: SourceLoc,
    ) -> Vec<PPToken> {
        // Bolt ⚡: Optimized macro expansion token creation.
        // This function is a hot path during macro expansion. We've optimized it by:
        // 1. Using a single pass to build the virtual buffer and collect token metadata.
        // 2. Caching SourceId lookups and 'is_pasted' checks to avoid redundant HashMap
        //    lookups and string comparisons for tokens from the same source.
        // 3. Avoiding redundant calls to `get_text()` by using the buffer lengths directly.
        // 4. Pre-allocating all necessary vectors with the correct capacity.

        // Pass 0: Sum up lengths for capacity hint.
        let total_upper_bound: usize = tokens.iter().map(|t| t.length as usize).sum();
        let mut buffer = Vec::with_capacity(total_upper_bound);

        // Metadata to avoid re-calculating things in the final mapping pass.
        // (is_pasted, offset_in_new_buffer, length_in_new_buffer)
        let mut token_metadata = Vec::with_capacity(tokens.len());

        let mut last_is_pasted_sid = None;
        let mut last_is_pasted_val = false;

        {
            let mut cache = SourceBufferCache::new(self.sm);

            for t in tokens {
                let sid = t.location.source_id();

                // Optimized is_pasted check with caching.
                let is_pasted = if Some(sid) == last_is_pasted_sid {
                    last_is_pasted_val
                } else {
                    let val = self
                        .sm
                        .get_file_info(sid)
                        .is_some_and(|info| info.kind == FileKind::PastedToken);
                    last_is_pasted_sid = Some(sid);
                    last_is_pasted_val = val;
                    val
                };

                let start_offset = buffer.len() as u32;

                // Build buffer efficiently using cache
                let bytes = cache.get_token_bytes(t);
                buffer.extend_from_slice(bytes);

                let len = (buffer.len() as u32 - start_offset) as u16;
                token_metadata.push((is_pasted, start_offset, len));
            }
        }

        let virtual_id = self.sm.add_virtual_buffer(
            buffer,
            &format!("macro_{}", macro_name),
            Some(trigger_location),
            FileKind::MacroExpansion,
        );

        // Final pass: Construct new tokens using the pre-calculated metadata.
        tokens
            .iter()
            .zip(token_metadata)
            .map(|(t, (is_pasted, offset, len))| {
                let loc = if is_pasted {
                    t.location
                } else {
                    SourceLoc::new(virtual_id, offset)
                };

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

    /// Helper to report error diagnostics from PPError
    fn report_pp_error(&mut self, err: PPError) {
        use crate::diagnostic::IntoDiagnostic;
        let diags = err.into_diagnostic();
        for diag in diags {
            self.diag.report_diagnostic(diag);
        }
    }

    /// Helper to report error diagnostics
    fn report_error(&mut self, message: impl Into<String>, loc: SourceLoc) {
        let span = SourceSpan::new(loc, loc);
        self.report_diagnostic(DiagnosticLevel::Error, message, span, None, Vec::new(), Vec::new());
    }

    /// Helper to report warning diagnostics
    fn report_warning(&mut self, message: impl Into<String>, loc: SourceLoc) {
        let span = SourceSpan::new(loc, loc);
        self.report_diagnostic(DiagnosticLevel::Warning, message, span, None, Vec::new(), Vec::new());
    }

    fn parse_macro_definition_params(
        &mut self,
        macro_name: &str,
    ) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
        let mut flags = MacroFlags::FUNCTION_LIKE;
        let mut params = Vec::new();
        let mut variadic = None;

        'param_parsing: loop {
            let param_token = self.expect_token()?;
            match param_token.kind {
                PPTokenKind::RightParen => break,
                PPTokenKind::Ellipsis => {
                    flags |= MacroFlags::C99_VARARGS;
                    variadic = Some(StringId::new("__VA_ARGS__"));
                    if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                        return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, param_token.location);
                    }
                    break;
                }
                PPTokenKind::Identifier(sym) => {
                    if params.contains(&sym) {
                        return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, param_token.location);
                    }
                    params.push(sym);

                    let sep = self.expect_token()?;
                    match sep.kind {
                        PPTokenKind::Comma => continue,
                        PPTokenKind::RightParen => break,
                        PPTokenKind::Ellipsis => {
                            variadic = Some(params.pop().unwrap());
                            flags |= MacroFlags::GNU_VARARGS;
                            if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                                return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, sep.location);
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
                    self.report_warning(
                        format!("Invalid macro parameter token in #define '{}'", macro_name),
                        param_token.location,
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

/// Helper to cache source buffers for efficient token text retrieval
struct SourceBufferCache<'a> {
    sm: &'a SourceManager,
    last_sid: Option<SourceId>,
    last_buffer: Option<&'a [u8]>,
}

impl<'a> SourceBufferCache<'a> {
    fn new(sm: &'a SourceManager) -> Self {
        Self {
            sm,
            last_sid: None,
            last_buffer: None,
        }
    }

    fn reset(&mut self) {
        self.last_sid = None;
        self.last_buffer = None;
    }

    fn get_token_bytes<'b>(&'b mut self, token: &'b PPToken) -> &'b [u8] {
        let sid = token.location.source_id();
        let buffer = if self.last_sid == Some(sid) {
            self.last_buffer.unwrap()
        } else if let Some(b) = self.sm.get_buffer_safe(sid) {
            // Bolt ⚡: Cache the buffer for the current source ID.
            self.last_sid = Some(sid);
            self.last_buffer = Some(b);
            b
        } else {
            // Fallback for built-in tokens or tokens without a physical buffer.
            return token.get_text().as_bytes();
        };

        let start = token.location.offset() as usize;
        let end = start + token.length as usize;
        if end <= buffer.len() {
            &buffer[start..end]
        } else {
            token.get_text().as_bytes()
        }
    }

    fn get_token_text<'b>(&'b mut self, token: &'b PPToken) -> &'b str {
        // Safety: Tokens are guaranteed to be valid UTF-8 by the lexer.
        unsafe { std::str::from_utf8_unchecked(self.get_token_bytes(token)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::StringId;

    #[test]
    fn test_is_directive() {
        let table = DirectiveKeywordTable::new();

        // Test known directive
        let define_sym = StringId::new("define");
        assert_eq!(table.is_directive(define_sym), Some(DirectiveKind::Define));

        // Test unknown directive (this covers the else { None } branch)
        let unknown_sym = StringId::new("not_a_directive");
        assert_eq!(table.is_directive(unknown_sym), None);
    }
}
