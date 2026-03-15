use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::lang_options::CStandard;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use hashbrown::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use super::pp_lexer::PPLexer;
use crate::pp::error::{PPError, PPErrorKind};
use crate::pp::interpreter::Interpreter;
use crate::pp::types::{
    DirectiveKeywordTable, HideSetTable, IncludeStackInfo, MacroFlags, MacroInfo, PPConditionalInfo, PPConfig,
};
use crate::pp::{HeaderSearch, PPToken, PPTokenFlags, PPTokenKind};
use std::path::Path;
use target_lexicon::{Architecture, OperatingSystem, Triple};

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    pub(crate) sm: &'src mut SourceManager,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) c_standard: CStandard,
    pub(crate) target: Triple,

    // Pre-interned directive keywords for fast comparison
    pub(crate) directive_keywords: DirectiveKeywordTable,

    // Macro management
    pub(crate) macros: HashMap<StringId, MacroInfo>,
    pub(crate) hide_sets: HideSetTable,
    pub(crate) macro_stack: HashMap<StringId, Vec<Option<MacroInfo>>>,

    // Include management
    pub(crate) once_included: HashSet<SourceId>,

    // Conditional compilation state
    pub(crate) conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    pub(crate) include_stack: Vec<IncludeStackInfo>,
    pub(crate) header_search: HeaderSearch,
    pub(crate) built_in_headers: HashMap<&'static str, &'static str>,
    pub(crate) built_in_file_ids: HashMap<String, SourceId>,

    // Token management
    pub(crate) lexer_stack: Vec<PPLexer>,
    // Bolt ⚡: Use a Vec instead of a VecDeque for the pending tokens stack.
    // The preprocessor uses this exclusively as a LIFO stack (push/pop).
    // Vec is more efficient than VecDeque as it avoids ring-buffer overhead,
    // provides better cache locality, and allows for efficient batch pushes
    // using `.extend()` with reversed iterators during macro expansion.
    pub(crate) pending_tokens: Vec<PPToken>,

    // State
    pub(crate) include_depth: usize,
    pub(crate) max_include_depth: usize,
    pub(crate) counter: u32,
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
        built_in_headers.insert("stdatomic.h", include_str!("../../custom-include/stdatomic.h"));
        built_in_headers.insert("limits.h", include_str!("../../custom-include/limits.h"));
        built_in_headers.insert("float.h", include_str!("../../custom-include/float.h"));

        let mut preprocessor = Preprocessor {
            sm: source_manager,
            diag,
            c_standard: config.c_standard,
            directive_keywords: DirectiveKeywordTable::new(),
            macros: HashMap::new(),
            hide_sets: HideSetTable::new(),
            macro_stack: HashMap::new(),
            once_included: HashSet::new(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            built_in_headers,
            built_in_file_ids: HashMap::new(),
            lexer_stack: Vec::new(),
            pending_tokens: Vec::new(),
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
    pub(crate) fn try_expand_magic_macro(&mut self, token: &PPToken) -> Option<PPToken> {
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

        Some(PPToken::text(kind, PPTokenFlags::MACRO_EXPANDED, token.location, &text))
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

        // Type limits
        self.define_builtin_macro_with_val("__CHAR_BIT__", "8");
        self.define_builtin_macro_with_val("__SCHAR_MAX__", "127");
        self.define_builtin_macro_with_val("__SHRT_MAX__", "32767");
        self.define_builtin_macro_with_val("__INT_MAX__", "2147483647");
        self.define_builtin_macro_with_val("__LONG_LONG_MAX__", "9223372036854775807LL");

        // Type sizes
        self.define_builtin_macro_with_val("__SIZEOF_SHORT__", "2");
        self.define_builtin_macro_with_val("__SIZEOF_INT__", "4");
        self.define_builtin_macro_with_val("__SIZEOF_LONG_LONG__", "8");
        self.define_builtin_macro_with_val("__SIZEOF_FLOAT__", "4");
        self.define_builtin_macro_with_val("__SIZEOF_DOUBLE__", "8");
        self.define_builtin_macro_with_val("__SIZEOF_LONG_DOUBLE__", "16");

        // Float limits
        self.define_builtin_macro_with_val("__FLT_MANT_DIG__", "24");
        self.define_builtin_macro_with_val("__DBL_MANT_DIG__", "53");
        self.define_builtin_macro_with_val("__LDBL_MANT_DIG__", "64");

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
            self.define_builtin_macro_with_val("__LONG_MAX__", "9223372036854775807L");
            self.define_builtin_macro_with_val("__SIZEOF_LONG__", "8");
            self.define_builtin_macro_with_val("__SIZEOF_POINTER__", "8");
        } else {
            for macro_name in &["__ILP32__", "_ILP32"] {
                self.define_builtin_macro_one(macro_name);
            }
            self.define_builtin_macro_with_val("__LONG_MAX__", "2147483647L");
            self.define_builtin_macro_with_val("__SIZEOF_LONG__", "4");
            self.define_builtin_macro_with_val("__SIZEOF_POINTER__", "4");
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

        // Atomic memory ordering constants
        self.define_builtin_macro_with_val("__ATOMIC_RELAXED", "0");
        self.define_builtin_macro_with_val("__ATOMIC_CONSUME", "1");
        self.define_builtin_macro_with_val("__ATOMIC_ACQUIRE", "2");
        self.define_builtin_macro_with_val("__ATOMIC_RELEASE", "3");
        self.define_builtin_macro_with_val("__ATOMIC_ACQ_REL", "4");
        self.define_builtin_macro_with_val("__ATOMIC_SEQ_CST", "5");

        // Sync compare and swap availability
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_1");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_2");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_8");

        if self.c_standard.is_c11() {
            self.define_builtin_macro_with_val("__STDC_VERSION__", "201112L");
            self.define_builtin_macro_one("__STDC_HOSTED__");
            self.define_builtin_macro_one("__STDC_MB_MIGHT_NEQ_WC__");
            self.define_builtin_macro_one("__STDC_IEC_559__");
            self.define_builtin_macro_one("__STDC_IEC_559_COMPLEX__");
            self.define_builtin_macro_with_val("__STDC_ISO_10646__", "201706L");
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
    pub(super) fn defined_symbol(&self) -> StringId {
        self.directive_keywords.defined_symbol()
    }

    /// Get the interned symbol for the "__has_include" operator
    pub(super) fn has_include_symbol(&self) -> StringId {
        self.directive_keywords.has_include_symbol()
    }

    /// Get the interned symbol for the "__has_include_next" operator
    pub(super) fn has_include_next_symbol(&self) -> StringId {
        self.directive_keywords.has_include_next_symbol()
    }

    /// Get the interned symbol for the "__has_builtin" operator
    pub(super) fn has_builtin_symbol(&self) -> StringId {
        self.directive_keywords.has_builtin_symbol()
    }

    /// Get the interned symbol for the "__has_attribute" operator
    pub(super) fn has_attribute_symbol(&self) -> StringId {
        self.directive_keywords.has_attribute_symbol()
    }

    /// Get the interned symbol for the "__has_feature" operator
    pub(super) fn has_feature_symbol(&self) -> StringId {
        self.directive_keywords.has_feature_symbol()
    }

    /// Get the interned symbol for the "__has_extension" operator
    pub(super) fn has_extension_symbol(&self) -> StringId {
        self.directive_keywords.has_extension_symbol()
    }

    /// Get the text associated with a token
    pub(super) fn get_token_text(&self, token: &PPToken) -> &str {
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
    pub(super) fn check_header_exists(&self, path: &str, is_angled: bool) -> bool {
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
    pub(super) fn check_next_header_exists(&self, path: &str, is_angled: bool) -> bool {
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
    pub(crate) fn expect_eod(&mut self) -> Result<(), PPError> {
        match self.lex_token() {
            Some(token) if token.kind == PPTokenKind::Eod => Ok(()),
            None => Ok(()), // End of file is acceptable
            Some(token) => self.emit_error_loc(PPErrorKind::ExpectedEod, token.location),
        }
    }

    /// Expect a token, and fail with UnexpectedEndOfFile if None is returned
    pub(crate) fn expect_token(&mut self) -> Result<PPToken, PPError> {
        self.lex_token()
            .ok_or_else(|| self.error(PPErrorKind::UnexpectedEndOfFile, self.get_current_span()))
    }

    /// Expect a token of a specific kind
    pub(crate) fn expect_kind(&mut self, kind: PPTokenKind) -> Result<PPToken, PPError> {
        let token = self.expect_token()?;
        if token.kind == kind {
            Ok(token)
        } else {
            self.emit_error_loc(PPErrorKind::InvalidDirective, token.location)
        }
    }

    /// Expect a string literal token
    pub(crate) fn expect_string_literal(&mut self) -> Result<(StringId, SourceLoc), PPError> {
        let token = self.expect_token()?;
        if let PPTokenKind::StringLiteral(s) = token.kind {
            Ok((s, token.location))
        } else {
            self.emit_error_loc(PPErrorKind::InvalidDirective, token.location)
        }
    }

    /// Expect an identifier token
    pub(crate) fn expect_identifier(&mut self) -> Result<(PPToken, StringId), PPError> {
        let token = self.expect_token()?;
        if let PPTokenKind::Identifier(sym) = token.kind {
            Ok((token, sym))
        } else {
            self.emit_error_loc(PPErrorKind::ExpectedIdentifier, token.location)
        }
    }

    /// Collect tokens balanced between open and close delimiters.
    /// Assumes the opening delimiter has NOT been consumed yet and will consume it.
    pub(crate) fn collect_balanced_tokens(
        &mut self,
        open: PPTokenKind,
        close: PPTokenKind,
    ) -> Result<Vec<PPToken>, PPError> {
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
    pub(crate) fn extract_string_literal_content(
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

        // ⚡ Bolt: Pre-allocate the result_tokens vector using a capacity hint based on buffer size.
        // A common estimate for C code is around 8 bytes per token.
        // This avoids multiple costly reallocations for large source files.
        let mut result_tokens = Vec::with_capacity(buffer_len as usize / 8);

        while let Some(token) = self.lex_token() {
            match token.kind {
                // Handle directive
                PPTokenKind::Hash
                    if !token.flags.contains(PPTokenFlags::MACRO_EXPANDED)
                        && token.flags.contains(PPTokenFlags::STARTS_PP_LINE) =>
                {
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
                        // Bolt ⚡: Efficiently push expanded tokens onto the stack.
                        // Using `.extend()` with a reversed iterator is significantly faster than
                        // a manual loop of individual `push_front` calls on a VecDeque.
                        self.pending_tokens.extend(expanded.into_iter().rev());
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
    pub(crate) fn get_current_location(&self) -> SourceLoc {
        if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
        } else {
            SourceLoc::builtin()
        }
    }

    pub(crate) fn get_current_span(&self) -> SourceSpan {
        let loc = self.get_current_location();
        SourceSpan::new(loc, loc)
    }

    fn error(&self, kind: PPErrorKind, span: SourceSpan) -> PPError {
        PPError { kind, span }
    }

    pub(crate) fn error_loc(&self, kind: PPErrorKind, loc: SourceLoc) -> PPError {
        PPError {
            kind,
            span: SourceSpan::new(loc, loc),
        }
    }

    pub(crate) fn emit_error<T>(&self, kind: PPErrorKind, span: SourceSpan) -> Result<T, PPError> {
        Err(PPError { kind, span })
    }

    pub(crate) fn emit_error_loc<T>(&self, kind: PPErrorKind, loc: SourceLoc) -> Result<T, PPError> {
        Err(PPError {
            kind,
            span: SourceSpan::new(loc, loc),
        })
    }

    /// Check if we are currently skipping tokens
    pub(crate) fn is_currently_skipping(&self) -> bool {
        // Bolt ⚡: Optimized to O(1) by checking only the top of the stack.
        // The skipping state is propagated downwards to ensure this is sufficient.
        self.conditional_stack.last().is_some_and(|info| info.was_skipping)
    }

    /// Parse a conditional expression for #if and #elif
    pub(crate) fn parse_conditional_expression(&mut self) -> Result<Vec<PPToken>, PPError> {
        // ⚡ Bolt: Use a small initial capacity to avoid reallocations for common short expressions.
        let mut tokens = Vec::with_capacity(16);
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
    pub(crate) fn evaluate_conditional_expression(&mut self, tokens: Vec<PPToken>) -> Result<bool, PPError> {
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
                    self.get_current_location(),
                    "Failed to expand macros in conditional expression",
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
                    self.get_current_location(),
                    "Invalid conditional expression in preprocessor directive",
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
    pub(crate) fn lex_token(&mut self) -> Option<PPToken> {
        if let Some(token) = self.pending_tokens.pop() {
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

    /// Skip current directive tokens until EOD
    pub(crate) fn skip_directive(&mut self) -> Result<(), PPError> {
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
        }
        Ok(())
    }

    /// Push a conditional that is lazily skipped (nested in a skipped block)
    pub(crate) fn push_skipped_conditional(&mut self) {
        // Bolt ⚡: Optimized to avoid redundant set_skipping call.
        let info = PPConditionalInfo {
            was_skipping: true,
            found_else: false,
            found_non_skipping: false, // Condition treated as false
        };
        self.conditional_stack.push(info);
    }

    /// Check if we should evaluate conditional expression (e.g. for #elif)
    pub(crate) fn should_evaluate_conditional(&self) -> bool {
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

    /// Helper to report diagnostics
    pub(crate) fn report_diagnostic(&mut self, level: DiagnosticLevel, message: impl Into<String>, span: SourceSpan) {
        let diag = Diagnostic {
            level,
            message: message.into(),
            span,
            hints: Vec::new(),
            warning_name: None,
        };
        self.diag.report_diagnostic(diag);
    }

    /// Helper to report error diagnostics from PPError
    pub(crate) fn report_pp_error(&mut self, err: PPError) {
        use crate::diagnostic::IntoDiagnostic;
        let diags = err.into_diagnostic();
        for diag in diags {
            self.diag.report_diagnostic(diag);
        }
    }

    /// Helper to report error diagnostics
    pub(crate) fn report_error(&mut self, loc: SourceLoc, message: impl Into<String>) {
        let span = SourceSpan::new(loc, loc);
        self.report_diagnostic(DiagnosticLevel::Error, message, span);
    }

    /// Helper to report warning diagnostics
    pub(crate) fn report_warning(&mut self, loc: SourceLoc, message: impl Into<String>) {
        let span = SourceSpan::new(loc, loc);
        self.report_diagnostic(DiagnosticLevel::Warning, message, span);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::StringId, pp::types::DirectiveKind};

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

    #[test]
    fn test_hide_set_table() {
        use smallvec::smallvec;
        let mut table = HideSetTable::new();
        let s1 = StringId::new("a");
        let s2 = StringId::new("b");
        let s3 = StringId::new("c");

        // Test intern
        let id0 = 0;
        let id1 = table.intern(smallvec![s1]);
        let id2 = table.intern(smallvec![s2]);
        let id1_again = table.intern(smallvec![s1]);
        let id12 = table.intern(smallvec![s2, s1]); // Should be sorted to [s1, s2]

        assert_eq!(id1, id1_again);
        assert_ne!(id1, id2);
        assert_ne!(id1, id12);
        assert_ne!(id2, id12);

        // Test contains
        assert!(table.contains(id1, s1));
        assert!(!table.contains(id1, s2));
        assert!(table.contains(id12, s1));
        assert!(table.contains(id12, s2));
        assert!(!table.contains(id0, s1));

        // Test insert
        let id12_from_1 = table.insert(id1, s2);
        assert_eq!(id12_from_1, id12);
        let id1_from_1 = table.insert(id1, s1);
        assert_eq!(id1_from_1, id1);

        // Test union
        let u12 = table.union(id1, id2);
        assert_eq!(u12, id12);
        let u11 = table.union(id1, id1);
        assert_eq!(u11, id1);
        let u01 = table.union(id0, id1);
        assert_eq!(u01, id1);

        // Test intersection
        let i12 = table.intersection(id1, id12);
        assert_eq!(i12, id1);
        let i12_2 = table.intersection(id2, id12);
        assert_eq!(i12_2, id2);
        let i12_none = table.intersection(id1, id2);
        assert_eq!(i12_none, id0);
        let i01 = table.intersection(id0, id1);
        assert_eq!(i01, id0);

        // Complex case
        let id123 = table.intern(smallvec![s1, s2, s3]);
        let id13 = table.intern(smallvec![s1, s3]);
        assert_eq!(table.union(id13, id12), id123);
        assert_eq!(table.intersection(id13, id12), id1);
    }
}
