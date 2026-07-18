use super::pp_lexer::PPLexer;
use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::lang_options::{LangOptions, PedanticMode};
use crate::pp::error::{PPDiag, PPError};
use crate::pp::interpreter::Interpreter;
use crate::pp::keyword_table::PPKeywordTable;
use crate::pp::types::{HideSetTable, IncludeStackInfo, MacroInfo, PPConditionalInfo, PPConfig};
use crate::pp::{HeaderSearch, PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager, SourceSpan};
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::{Path, PathBuf};
use target_lexicon::Triple;

/// Main preprocessor structure
pub struct Preprocessor<'src> {
    pub(crate) sm: &'src mut SourceManager,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) target: Triple,
    pub(crate) lang_options: LangOptions,

    // Pre-interned directive keywords for fast comparison
    pub(crate) keywords: PPKeywordTable,

    // Macro management
    pub(crate) macros: FxHashMap<StringId, MacroInfo>,
    pub(crate) hide_sets: HideSetTable,
    pub(crate) macro_stack: FxHashMap<StringId, Vec<Option<MacroInfo>>>,

    // Conditional compilation state
    pub(crate) conditional_stack: Vec<PPConditionalInfo>,

    // Include handling
    pub(crate) once_included: FxHashSet<SourceId>,
    pub(crate) include_stack: Vec<IncludeStackInfo>,
    pub(crate) header_search: HeaderSearch,
    pub(crate) built_in_headers: FxHashMap<&'static str, &'static str>,
    pub(crate) built_in_file_ids: FxHashMap<String, SourceId>,

    // Token management
    pub(crate) lexer_stack: Vec<PPLexer>,
    pub(crate) pending_tokens: Vec<PPToken>,

    // State
    pub(super) include_depth: usize,
    pub(super) max_include_depth: usize,
    counter: u32,
    pub(super) in_macro_argument_parsing: usize,
    eof_emitted: bool,
    pub(super) poisoned_identifiers: FxHashSet<StringId>,
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

        let mut built_in_headers = FxHashMap::default();
        built_in_headers.insert("stddef.h", include_str!("../../custom-include/stddef.h"));
        built_in_headers.insert("stdint.h", include_str!("../../custom-include/stdint.h"));
        built_in_headers.insert("stdarg.h", include_str!("../../custom-include/stdarg.h"));
        built_in_headers.insert("stdbool.h", include_str!("../../custom-include/stdbool.h"));
        built_in_headers.insert("stdatomic.h", include_str!("../../custom-include/stdatomic.h"));
        built_in_headers.insert("limits.h", include_str!("../../custom-include/limits.h"));
        built_in_headers.insert("float.h", include_str!("../../custom-include/float.h"));
        built_in_headers.insert("complex.h", include_str!("../../custom-include/complex.h"));

        let mut preprocessor = Preprocessor {
            sm: source_manager,
            diag,
            keywords: PPKeywordTable::new(),
            macros: FxHashMap::default(),
            hide_sets: HideSetTable::new(),
            macro_stack: FxHashMap::default(),
            once_included: FxHashSet::default(),
            conditional_stack: Vec::new(),
            include_stack: Vec::new(),
            header_search,
            built_in_headers,
            built_in_file_ids: FxHashMap::default(),
            lexer_stack: Vec::new(),
            pending_tokens: Vec::new(),
            include_depth: 0,
            max_include_depth: config.max_include_depth,
            target: config.target.clone(),
            lang_options: config.lang_options,
            counter: 0,
            in_macro_argument_parsing: 0,
            eof_emitted: false,
            poisoned_identifiers: FxHashSet::default(),
        };

        // Initialize built-in headers
        for (name, content) in &preprocessor.built_in_headers {
            let source_id = preprocessor.sm.add_buffer(
                content.as_bytes().to_vec(),
                name,
                None, // No include location for initialization
                FileKind::Builtin,
            );
            preprocessor.built_in_file_ids.insert(name.to_string(), source_id);
        }

        preprocessor.initialize_builtin_macros(config.current_time);
        preprocessor
    }

    /// Try to expand a magic macro (e.g. __LINE__, __FILE__, __COUNTER__)
    pub(super) fn try_expand_magic_macro(&mut self, token: &PPToken) -> Option<PPToken> {
        let PPTokenKind::Identifier(symbol) = token.kind else {
            return None;
        };

        let (kind, text) = match symbol {
            s if s == self.keywords.line_macro => {
                let line = self.sm.get_presumed_location(token.location).map(|p| p.0).unwrap_or(1);
                (PPTokenKind::Number, line.to_string())
            }
            s if s == self.keywords.file_macro => {
                let filename = self
                    .sm
                    .get_presumed_location(token.location)
                    .and_then(|p| p.2)
                    .unwrap_or("<unknown>");
                (PPTokenKind::StringLiteral, format!("\"{}\"", filename))
            }
            s if s == self.keywords.counter_macro => (PPTokenKind::Number, self.get_next_counter().to_string()),
            _ => return None,
        };

        let source_id = self.sm.add_buffer(
            text.as_bytes().to_vec(),
            "<magic-macro>",
            Some(token.location),
            FileKind::MacroExpansion,
        );
        let loc = SourceLoc::new(source_id, 0);

        let mut flags = PPTokenFlags::MACRO_EXPANDED;
        if token.flags.contains(PPTokenFlags::LEADING_SPACE) {
            flags |= PPTokenFlags::LEADING_SPACE;
        }
        Some(PPToken::text(kind, flags, loc, &text))
    }

    /// Get the next value for __COUNTER__
    fn get_next_counter(&mut self) -> u32 {
        let val = self.counter;
        self.counter += 1;
        val
    }

    /// Check if a macro is defined
    pub(crate) fn is_macro_defined(&self, symbol: StringId) -> bool {
        // Bolt ⚡: Optimization: Check self.macros FIRST. This is the common case
        // during macro expansion and #ifdef checks.
        if self.macros.contains_key(&symbol) {
            return true;
        }

        // Bolt ⚡: Use direct comparisons instead of a linear scan on a temporary array.
        // This avoids array initialization and iterator overhead.
        // Also includes magic macros (__LINE__, __FILE__, __COUNTER__) for better standard compliance.
        let kw = &self.keywords;
        symbol == kw.has_include
            || symbol == kw.has_include_next
            || symbol == kw.has_builtin
            || symbol == kw.has_attribute
            || symbol == kw.has_c_attribute
            || symbol == kw.has_feature
            || symbol == kw.has_extension
            || symbol == kw.line_macro
            || symbol == kw.file_macro
            || symbol == kw.counter_macro
    }

    /// Get the current directory of the file at the top of the lexer stack
    pub(super) fn get_current_dir(&self) -> &Path {
        self.lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."))
    }

    /// Load a header file from a resolved path
    pub(super) fn load_resolved_header(
        &mut self,
        path: &str,
        resolved: Option<PathBuf>,
        loc: SourceLoc,
    ) -> Result<Option<SourceId>, PPDiag> {
        if let Some(path_buf) = resolved {
            let id = self
                .sm
                .add_file(&path_buf, Some(loc))
                .map_err(|_| self.error(PPError::FileNotFound { path: path.to_string() }, loc))?;
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    /// Check if a header exists
    pub(super) fn check_header_exists(&self, path: &str, is_angled: bool) -> bool {
        let current_dir = self.get_current_dir();

        if is_angled && self.built_in_headers.contains_key(path) {
            return true;
        }

        self.header_search.resolve_path(path, is_angled, current_dir).is_some()
            || (!is_angled && self.sm.get_file_id(path).is_some())
    }

    /// Check if a header exists for #include_next
    pub(super) fn check_next_header_exists(&self, path: &str, is_angled: bool) -> bool {
        let current_dir = self.get_current_dir();

        if self
            .header_search
            .resolve_next_path(path, is_angled, current_dir)
            .is_some()
        {
            return true;
        }

        // If not found as "next", and we are in the main file, treat as normal include
        // some compilers do this to allow __has_include_next to work in tests
        if self.lexer_stack.len() == 1 {
            return self.check_header_exists(path, is_angled);
        }

        false
    }

    /// Expect and consume an Eod token or end of file
    pub(super) fn expect_eod(&mut self) -> Result<(), PPDiag> {
        match self.lex_token() {
            Some(token) if token.kind == PPTokenKind::Eod => Ok(()),
            None => Ok(()), // End of file is acceptable
            Some(token) => self.emit_error(PPError::ExpectedEod, token.location),
        }
    }

    /// Expect a token, and fail with UnexpectedEndOfFile if None is returned
    pub(super) fn expect_token(&mut self) -> Result<PPToken, PPDiag> {
        self.lex_token()
            .ok_or_else(|| self.error_span(PPError::UnexpectedEndOfFile, self.get_current_span()))
    }

    /// Expect a token of a specific kind
    pub(super) fn expect_kind(&mut self, kind: PPTokenKind) -> Result<PPToken, PPDiag> {
        let token = self.expect_token()?;
        if token.kind == kind {
            Ok(token)
        } else {
            self.emit_error(PPError::InvalidDirective, token.location)
        }
    }

    /// Expect a string literal token
    pub(super) fn expect_string_literal(&mut self) -> Result<(String, SourceLoc), PPDiag> {
        let token = self.expect_token()?;
        if let PPTokenKind::StringLiteral = token.kind {
            Ok((token.get_text(self.sm).to_string(), token.location))
        } else {
            self.emit_error(PPError::InvalidDirective, token.location)
        }
    }

    /// Expect an identifier token
    pub(super) fn expect_identifier(&mut self) -> Result<(PPToken, StringId), PPDiag> {
        let token = self.expect_token()?;
        if let PPTokenKind::Identifier(sym) = token.kind {
            Ok((token, sym))
        } else {
            self.emit_error(PPError::ExpectedIdentifier, token.location)
        }
    }

    /// Collect tokens balanced between open and close delimiters.
    /// Assumes the opening delimiter has NOT been consumed yet and will consume it.
    pub(super) fn collect_balanced_tokens(
        &mut self,
        open: PPTokenKind,
        close: PPTokenKind,
    ) -> Result<Vec<PPToken>, PPDiag> {
        self.expect_kind(open)?;
        // ⚡ Bolt: Use a small initial capacity to avoid reallocations for common short expressions.
        let mut tokens = Vec::with_capacity(8);
        let mut depth = 1;
        while let Some(t) = self.lex_token() {
            if t.kind == PPTokenKind::Eod {
                return self.emit_error(PPError::UnexpectedEndOfFile, t.location);
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
        self.emit_error(PPError::UnexpectedEndOfFile, self.get_current_location())
    }

    /// Helper to extract content of a string literal, stripping quotes.
    pub(super) fn extract_literal_content<'a>(
        &self,
        text: &'a str,
        location: SourceLoc,
        error_kind: PPError,
    ) -> Result<&'a str, PPDiag> {
        text.strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .ok_or_else(|| self.error(error_kind, location))
    }

    /// Process source file and return preprocessed tokens
    /// Start processing a source file by initializing the lexer stack
    pub(crate) fn start_processing(&mut self, source_id: SourceId) {
        self.push_lexer(source_id, false);
    }

    /// Retrieve the next fully processed and expanded token from the preprocessor stream
    pub(crate) fn next_token_with_directives(&mut self) -> Result<Option<PPToken>, PPDiag> {
        while let Some(token) = self.lex_token() {
            match token.kind {
                // Handle directive
                PPTokenKind::Hash
                    if !token.flags.contains(PPTokenFlags::MACRO_EXPANDED)
                        && token.flags.contains(PPTokenFlags::STARTS_PP_LINE) =>
                {
                    if self.in_macro_argument_parsing > 0 {
                        let err = self.error(PPError::DirectiveInMacroArgs, token.location);
                        self.report_pp_warning(err);
                    }
                    self.handle_directive()?;
                }
                // Skip tokens when in conditional compilation skip mode
                _ if self.is_currently_skipping() => {
                    // Bolt ⚡: When skipping a disabled block, use the fast-path in the lexer
                    // to jump directly to the next potential directive.
                    if self.pending_tokens.is_empty()
                        && let Some(lexer) = self.lexer_stack.last_mut()
                    {
                        lexer.fast_skip_to_directive();
                    }
                    continue;
                }
                // Skip Eod tokens
                PPTokenKind::Eod => continue,
                _ => return Ok(Some(token)),
            }
        }
        Ok(None)
    }

    /// Retrieve the next fully processed and expanded token from the preprocessor stream
    pub(crate) fn next_token(&mut self) -> Result<Option<PPToken>, PPDiag> {
        while let Some(token) = self.next_token_with_directives()? {
            match token.kind {
                // Handle identifiers (macros, magic macros, _Pragma)
                PPTokenKind::Identifier(symbol) => {
                    if let Some(magic) = self.try_expand_magic_macro(&token) {
                        return Ok(Some(magic));
                    } else if symbol == self.keywords.pragma_operator {
                        self.handle_pragma_operator()?;
                    } else if let Some(expanded) = self.expand_macro(&token)? {
                        if !expanded.is_empty() {
                            let mut expanded = expanded;
                            if token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                                expanded[0].flags |= PPTokenFlags::LEADING_SPACE;
                            } else {
                                expanded[0].flags &= !PPTokenFlags::LEADING_SPACE;
                            }
                            self.pending_tokens.extend(expanded.into_iter().rev());
                        }
                    } else {
                        return Ok(Some(token));
                    }
                }
                // All other tokens
                _ => return Ok(Some(token)),
            }
        }

        // Ensure we catch unbalanced conditionals at EOF
        if !self.conditional_stack.is_empty() {
            let loc = self.get_current_location();
            // Clear the stack so we don't infinitely report this error on subsequent calls
            self.conditional_stack.clear();
            return self.emit_error(PPError::UnclosedConditional, loc);
        }

        if !self.eof_emitted {
            self.eof_emitted = true;
            return Ok(Some(PPToken::simple(PPTokenKind::Eof, self.get_current_location())));
        }

        Ok(None)
    }

    /// Process source file and return preprocessed tokens (for non-streaming compatibility)
    pub(crate) fn process(&mut self, source_id: SourceId) -> Result<Vec<PPToken>, PPDiag> {
        let buffer_len = self.sm.get_buffer(source_id).len() as u32;
        self.start_processing(source_id);

        let mut result_tokens = Vec::with_capacity(buffer_len as usize / 8);

        while let Some(token) = self.next_token()? {
            result_tokens.push(token);
        }

        Ok(result_tokens)
    }

    /// Get the current location from the lexer stack
    pub(super) fn get_current_location(&self) -> SourceLoc {
        if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
        } else {
            SourceLoc::builtin()
        }
    }

    pub(super) fn get_current_span(&self) -> SourceSpan {
        let loc = self.get_current_location();
        SourceSpan::from_loc(loc)
    }

    fn error_span(&self, kind: PPError, span: SourceSpan) -> PPDiag {
        PPDiag { kind, span }
    }

    /// create PPError with SourceSpan from SourceLoc
    pub(super) fn error(&self, kind: PPError, loc: SourceLoc) -> PPDiag {
        PPDiag {
            kind,
            span: SourceSpan::from_loc(loc),
        }
    }

    pub(super) fn emit_error_span<T>(&self, kind: PPError, span: SourceSpan) -> Result<T, PPDiag> {
        Err(PPDiag { kind, span })
    }

    /// emit Result<PPError> with SourceSpan from SourceLoc
    pub(super) fn emit_error<T>(&self, kind: PPError, loc: SourceLoc) -> Result<T, PPDiag> {
        Err(self.error(kind, loc))
    }

    /// Collect tokens until Eod (end of directive line)
    pub(super) fn collect_tokens_until_eod(&mut self) -> Vec<PPToken> {
        let mut tokens = Vec::with_capacity(32);
        self.collect_tokens_into(&mut tokens);
        tokens
    }

    /// Collect tokens until Eod, including an already consumed initial token.
    pub(super) fn collect_tokens_until_eod_with_initial(&mut self, initial: PPToken) -> Vec<PPToken> {
        let mut tokens = Vec::with_capacity(32);
        tokens.push(initial);
        self.collect_tokens_into(&mut tokens);
        tokens
    }

    fn collect_tokens_into(&mut self, tokens: &mut Vec<PPToken>) {
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }
    }

    /// Check if we are currently skipping tokens
    pub(super) fn is_currently_skipping(&self) -> bool {
        // Bolt ⚡: Optimized to O(1) by checking only the top of the stack.
        // The skipping state is propagated downwards to ensure this is sufficient.
        self.conditional_stack.last().is_some_and(|info| info.was_skipping)
    }

    /// Evaluate a conditional expression (simplified - handle defined and basic arithmetic)
    pub(super) fn evaluate_conditional_expression(&mut self) -> Result<bool, PPDiag> {
        let mut tokens = self.collect_tokens_until_eod();
        match self.expand_tokens(&mut tokens, true) {
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

        if tokens.is_empty() {
            let loc = self.get_current_location();
            return self.emit_error(PPError::InvalidConditionalExpression, loc);
        }

        let mut interpreter = Interpreter::new(&tokens, self);
        let result = interpreter.evaluate();

        result.map(|val| val.is_truthy())
    }

    /// Push a new lexer onto the stack for the given source ID, increasing the include depth if this is an included file.
    pub(super) fn push_lexer(&mut self, source_id: SourceId, is_include: bool) {
        let buffer = self.sm.get_buffer_arc(source_id);
        self.lexer_stack.push(PPLexer::new(source_id, buffer));
        if is_include {
            self.include_stack.push(IncludeStackInfo { file_id: source_id });
            self.include_depth += 1;
        }
    }

    /// pop the current lexer from the stack, returning true if there are more lexers to process
    pub(super) fn pop_lexer(&mut self) -> bool {
        // EOF reached, pop the lexer
        let popped_lexer = self.lexer_stack.pop().unwrap();

        // If this was an included file, pop from include stack and decrement depth.
        if let Some(include_info) = self.include_stack.last()
            && include_info.file_id == popped_lexer.source_id
        {
            self.include_stack.pop();
            self.include_depth -= 1;
        }

        !self.lexer_stack.is_empty()
    }

    /// Lex the next token
    pub(super) fn lex_token(&mut self) -> Option<PPToken> {
        let token = self.lex_token_internal()?;
        // Bolt ⚡: Optimization: added fast-path check !self.poisoned_identifiers.is_empty()
        // before calling contains. This avoids redundant hashing and set lookups for
        // identifier tokens in projects that do not use #pragma GCC poison.
        if let PPTokenKind::Identifier(sym) = token.kind
            && !self.poisoned_identifiers.is_empty()
            && self.poisoned_identifiers.contains(&sym)
        {
            let err = self.error(PPError::PoisonedIdentifier(sym), token.location);
            self.report_pp_error(err);
        }
        Some(token)
    }

    fn lex_token_internal(&mut self) -> Option<PPToken> {
        if let Some(token) = self.pending_tokens.pop() {
            return Some(token);
        }

        while let Some(lexer) = self.lexer_stack.last_mut() {
            if let Some(token) = lexer.next_token() {
                if token.flags.contains(PPTokenFlags::HAS_INVALID_UCN) {
                    let err = self.error(PPError::InvalidUniversalCharacterName, token.location);
                    self.report_pp_error(err);
                }

                if self.lang_options.is_pedantic()
                    && matches!(token.kind, PPTokenKind::Identifier(_) | PPTokenKind::Number)
                    && token.get_text(self.sm).contains('$')
                {
                    let err = self.error(PPError::DollarInIdentifier, token.location);
                    self.report_pp_warning(err);
                }
                return Some(token);
            } else if self.pop_lexer() == false {
                return None;
            }
        }
        None
    }

    /// Skip current directive tokens until EOD/EOF
    pub(super) fn skip_directive(&mut self) -> Result<(), PPDiag> {
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
        }
        Ok(())
    }

    /// Push a conditional that is lazily skipped (nested in a skipped block)
    pub(super) fn push_skipped_conditional(&mut self) {
        // Bolt ⚡: Optimized to avoid redundant set_skipping call.
        let info = PPConditionalInfo {
            was_skipping: true,
            found_else: false,
            found_non_skipping: false, // Condition treated as false
        };
        self.conditional_stack.push(info);
    }

    /// Check if we should evaluate conditional expression (e.g. for #elif)
    pub(super) fn should_evaluate_conditional(&self) -> bool {
        let Some((current, rest)) = self.conditional_stack.split_last() else {
            return false;
        };
        let parent_skipping = rest.last().is_some_and(|info| info.was_skipping);
        !parent_skipping && !current.found_non_skipping
    }

    /// Helper to report diagnostics
    pub(super) fn report_diagnostic(&mut self, level: DiagnosticLevel, message: impl Into<String>, span: SourceSpan) {
        let diag = Diagnostic {
            level,
            message: message.into(),
            span,
            ..Default::default()
        };
        self.diag.report(diag, self.sm);
    }

    /// Helper to report error diagnostics from PPError
    pub(super) fn report_pp_error(&mut self, err: PPDiag) {
        use crate::diagnostic::IntoDiagnostic;
        let diags = err.into_diagnostic();
        for diag in diags {
            self.diag.report(diag, self.sm);
        }
    }

    pub(super) fn report_pp_warning(&mut self, err: PPDiag) {
        use crate::diagnostic::IntoDiagnostic;
        let is_pedantic = err.kind.is_pedantic();
        let mut diags = err.into_diagnostic();

        if is_pedantic {
            if self.lang_options.pedantic_mode == PedanticMode::Error {
                for diag in &mut diags {
                    diag.level = DiagnosticLevel::Error;
                }
            } else if self.lang_options.pedantic_mode == PedanticMode::Warning {
                for diag in &mut diags {
                    diag.level = DiagnosticLevel::Warning;
                }
            } else {
                return;
            }
        } else {
            for diag in &mut diags {
                diag.level = DiagnosticLevel::Warning;
            }
        }

        for diag in diags {
            self.diag.report(diag, self.sm);
        }
    }

    /// Helper to report error diagnostics
    pub(super) fn report_error(&mut self, loc: SourceLoc, message: impl Into<String>) {
        let span = SourceSpan::from_loc(loc);
        self.report_diagnostic(DiagnosticLevel::Error, message, span);
    }

    /// Helper to report warning diagnostics
    pub(super) fn report_warning(&mut self, loc: SourceLoc, message: impl Into<String>) {
        let span = SourceSpan::from_loc(loc);
        self.report_diagnostic(DiagnosticLevel::Warning, message, span);
    }

    /// Helper to report warning diagnostics with a warning name
    pub(super) fn report_warning_with_name(&mut self, loc: SourceLoc, message: impl Into<String>, name: &'static str) {
        let diag = Diagnostic {
            level: DiagnosticLevel::Warning,
            message: message.into(),
            span: SourceSpan::from_loc(loc),
            warning_name: Some(name),
            ..Default::default()
        };
        self.diag.report(diag, self.sm);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::StringId, pp::DirectiveKind};

    #[test]
    fn test_is_directive() {
        let table = PPKeywordTable::new();

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
        let id12 = table.intern(smallvec![s1, s2]);
        let id13 = table.intern(smallvec![s1, s3]);
        assert_eq!(table.intersection(id13, id12), id1);
    }
}
