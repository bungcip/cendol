use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use chrono::{DateTime, Datelike, Timelike, Utc};
use std::collections::{HashMap, HashSet};

use crate::pp::expr_parser::ExpressionParser;
use std::path::{Path, PathBuf};
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple as TargetInfo;

// Re-export types from pp_lexer module for backward compatibility
pub use crate::pp::pp_lexer::{PPLexer, PPToken, PPTokenFlags, PPTokenKind};

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
#[derive(Debug, Clone)]
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
    pub fn resolve_path(&self, include_path: &str, is_angled: bool, current_dir: &Path) -> Option<PathBuf> {
        if is_angled {
            for search_path in &self.search_path {
                let candidate = search_path.path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        } else {
            // quoted
            let candidate = current_dir.join(include_path);
            if candidate.exists() {
                return Some(candidate);
            }
            for search_path in &self.search_path {
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
pub struct SearchPath {
    pub path: PathBuf,
    pub is_system: bool,
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
    built_in_headers: HashMap<&'static str, &'static str>,

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

        let mut built_in_headers = HashMap::new();
        built_in_headers.insert("stddef.h", include_str!("../../custom-include/stddef.h"));
        built_in_headers.insert("stdarg.h", include_str!("../../custom-include/stdarg.h"));
        built_in_headers.insert("stdio.h", include_str!("../../custom-include/stdio.h"));

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
            built_in_headers,
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
            vec![PPToken::new(
                PPTokenKind::Number(Symbol::new("1")),
                PPTokenFlags::empty(),
                SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                1,
            )],
        );

        if self.lang_opts.c11 {
            self.define_builtin_macro(
                "__STDC_VERSION__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("201112")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    6,
                )],
            );
            self.define_builtin_macro(
                "__STDC_HOSTED__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_MB_MIGHT_NEQ_WC__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_IEC_559_COMPLEX__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("1")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    1,
                )],
            );
            self.define_builtin_macro(
                "__STDC_ISO_10646__",
                vec![PPToken::new(
                    PPTokenKind::Number(Symbol::new("201103L")),
                    PPTokenFlags::empty(),
                    SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
                    7,
                )],
            );
        }

        // Variadic argument macros
        // Define va_start as function-like macro expanding to va_start
        self.define_builtin_function_macro("va_start", vec![Symbol::new("ap"), Symbol::new("param")], vec![PPToken::new(
            PPTokenKind::Identifier(Symbol::new("va_start")),
            PPTokenFlags::empty(),
            SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
            7,
        )]);
        // Define va_end as function-like macro expanding to va_end
        self.define_builtin_function_macro("va_end", vec![Symbol::new("ap")], vec![PPToken::new(
            PPTokenKind::Identifier(Symbol::new("va_end")),
            PPTokenFlags::empty(),
            SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
            6,
        )]);
        // Define va_arg as function-like macro expanding to va_arg so the parser can detect it
        self.define_builtin_function_macro("va_arg", vec![Symbol::new("ap"), Symbol::new("type")], vec![PPToken::new(
            PPTokenKind::Identifier(Symbol::new("va_arg")),
            PPTokenFlags::empty(),
            SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
            6,
        )]);

    }

    /// Define a built-in macro
    fn define_builtin_macro(&mut self, name: &str, tokens: Vec<PPToken>) {
        let symbol = Symbol::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
            flags: MacroFlags::BUILTIN,
            tokens,
            parameter_list: Vec::new(),
            variadic_arg: None,
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Define a built-in function-like macro
    fn define_builtin_function_macro(&mut self, name: &str, params: Vec<Symbol>, tokens: Vec<PPToken>) {
        let symbol = Symbol::new(name);
        let macro_info = MacroInfo {
            location: SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
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
            PPTokenKind::StringLiteral(Symbol::new(s)),
            PPTokenFlags::empty(),
            SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0),
            s.len() as u16,
        )]
    }

    /// Check if a macro is defined
    pub fn is_macro_defined(&self, symbol: &Symbol) -> bool {
        self.macros.contains_key(symbol)
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
            match token.kind {
                PPTokenKind::Hash if token.flags.contains(PPTokenFlags::STARTS_PP_LINE) => {
                    // Handle directive - always process directives regardless of skipping
                    self.handle_directive()?;
                }
                _ => {
                    if self.is_currently_skipping() {
                        // Skip tokens when in conditional compilation skip mode
                        continue;
                    }

                    match token.kind {
                        PPTokenKind::Identifier(symbol) => {
                            if symbol.as_str() == "__LINE__" {
                                let line = if let Some(presumed) = self.source_manager.get_presumed_location(token.location) {
                                    presumed.0
                                } else {
                                    1
                                };
                                let line_str = line.to_string();
                                let line_symbol = Symbol::new(&line_str);
                                result_tokens.push(PPToken::new(
                                    PPTokenKind::Number(line_symbol),
                                    PPTokenFlags::empty(),
                                    token.location,
                                    line_str.len() as u16,
                                ));
                            } else {
                                // Check for macro expansion
                                if let Some(expanded) = self.expand_macro(&token)? {
                                    // Replace the macro identifier with expanded tokens
                                    result_tokens.extend(expanded);
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
        }

        // Add EOF token
        result_tokens.push(PPToken::new(
            PPTokenKind::Eof,
            PPTokenFlags::empty(),
            SourceLoc::new(source_id, buffer_len),
            0,
        ));

        Ok(result_tokens)
    }

    /// Get the current location from the lexer stack
    fn get_current_location(&self) -> SourceLoc {
        if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
        } else {
            SourceLoc::new(crate::source_manager::SourceId(std::num::NonZeroU32::new(1).unwrap()), 0)
        }
    }

    /// Check if we are currently skipping tokens
    fn is_currently_skipping(&self) -> bool {
        self.skipping || self.conditional_stack.iter().any(|info| info.was_skipping)
    }

    /// Set the skipping state
    fn set_skipping(&mut self, skipping: bool) {
        self.skipping = skipping;
    }

    /// Parse a conditional expression for #if and #elif
    fn parse_conditional_expression(&mut self) -> Result<Vec<PPToken>, PreprocessorError> {
        // Set expression mode for the lexer
        if let Some(lexer) = self.lexer_stack.last_mut() {
            lexer.in_expression = true;
        }

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
            let location = SourceSpan::new(self.get_current_location(), self.get_current_location());
            let diag = crate::diagnostic::Diagnostic {
                level: crate::diagnostic::DiagnosticLevel::Error,
                message: "Invalid conditional expression".to_string(),
                location,
                code: Some("invalid_conditional_expression".to_string()),
                hints: vec!["Conditional directives require an expression".to_string()],
                related: Vec::new(),
            };
            self.diag.report_diagnostic(diag);
            return Err(PreprocessorError::InvalidConditionalExpression);
        }

        // Reset expression mode
        if let Some(lexer) = self.lexer_stack.last_mut() {
            lexer.in_expression = false;
        }

        Ok(tokens)
    }

    /// Evaluate a conditional expression (simplified - handle defined and basic arithmetic)
    fn evaluate_conditional_expression(
        &mut self,
        tokens: &[PPToken],
    ) -> Result<bool, PreprocessorError> {
        if tokens.is_empty() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }

        // Check for defined(identifier) or defined identifier before macro expansion
        if tokens.len() >= 2
            && matches!(tokens[0].kind, PPTokenKind::Defined)
        {
            if tokens.len() == 2 {
                // defined identifier
                if let PPTokenKind::Identifier(sym) = &tokens[1].kind {
                    return Ok(self.macros.contains_key(sym));
                }
            } else if tokens.len() == 4
                && matches!(tokens[1].kind, PPTokenKind::LeftParen)
                && matches!(tokens[3].kind, PPTokenKind::RightParen)
            {
                // defined(identifier)
                if let PPTokenKind::Identifier(sym) = &tokens[2].kind {
                    return Ok(self.macros.contains_key(sym));
                }
            }
        }

        // First, expand macros in the expression
        let mut expanded_tokens = tokens.to_vec();
        self.expand_tokens(&mut expanded_tokens)?;

        // Evaluate arithmetic expression
        self.evaluate_arithmetic_expression(&expanded_tokens)
    }

    /// Evaluate a simple arithmetic expression for #if/#elif
    fn evaluate_arithmetic_expression(
        &mut self,
        tokens: &[PPToken],
    ) -> Result<bool, PreprocessorError> {
        if tokens.is_empty() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }


        let mut parser = ExpressionParser::new(tokens, self);
        let expr = match parser.parse_expression() {
            Ok(e) => e,
            Err(_) => {
                let location = if !tokens.is_empty() {
                    SourceSpan::new(tokens[0].location, tokens[0].location)
                } else {
                    SourceSpan::empty()
                };
                let diag = crate::diagnostic::Diagnostic {
                    level: crate::diagnostic::DiagnosticLevel::Error,
                    message: "Invalid conditional expression".to_string(),
                    location,
                    code: Some("invalid_conditional_expression".to_string()),
                    hints: vec!["Check the syntax of the conditional expression".to_string()],
                    related: Vec::new(),
                };
                self.diag.report_diagnostic(diag);
                return Err(PreprocessorError::InvalidConditionalExpression);
            }
        };
        let result = expr.evaluate(self)?;
        Ok(result != 0)
    }


    /// Lex the next token
    fn lex_token(&mut self) -> Option<PPToken> {
        loop {
            if let Some(lexer) = self.lexer_stack.last_mut() {
                if let Some(token) = lexer.next_token() {
                    return Some(token);
                } else {
                    // EOF reached, pop the lexer
                    let popped_lexer = self.lexer_stack.pop().unwrap();
                    // Set the line_starts from the lexer to the source manager
                    self.source_manager.set_line_starts(popped_lexer.source_id, popped_lexer.get_line_starts().clone());
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
            PPTokenKind::Identifier(sym) => {
                let name = sym.as_str();
                match name {
                    "define" => self.handle_define()?,
                    "undef" => self.handle_undef()?,
                    "include" => self.handle_include()?,
                    "if" => {
                        let expr_tokens = self.parse_conditional_expression()?;
                        let condition = self.evaluate_conditional_expression(&expr_tokens)?;
                        self.handle_if_directive(condition)?;
                    }
                    "ifdef" => {
                        self.handle_ifdef()?;
                    }
                    "ifndef" => {
                        self.handle_ifndef()?;
                    }
                    "elif" => {
                        let expr_tokens = self.parse_conditional_expression()?;
                        let condition = self.evaluate_conditional_expression(&expr_tokens)?;
                        self.handle_elif_directive(condition)?;
                    }
                    "else" => {
                        self.handle_else()?;
                    }
                    "endif" => {
                        self.handle_endif()?;
                    }
                    "line" => self.handle_line()?,
                    "pragma" => self.handle_pragma()?,
                    "error" => self.handle_error()?,
                    "warning" => self.handle_warning()?,
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
            }
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

        // Now, collect replacement tokens
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        let mut flags = MacroFlags::empty();
        let mut params = Vec::new();
        let mut variadic = None;
        let next = self.lex_token();
        if let Some(token) = next {
            if token.kind == PPTokenKind::LeftParen {
                let first_param = self.lex_token();
                if let Some(fp) = first_param {
                    if matches!(fp.kind, PPTokenKind::RightParen | PPTokenKind::Identifier(_) | PPTokenKind::Ellipsis) {
                        flags |= MacroFlags::FUNCTION_LIKE;
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(fp);
                        }
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
                    } else {
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(fp);
                            lexer.put_back(token);
                        }
                    }
                } else {
                    return Err(PreprocessorError::UnexpectedEndOfFile);
                }
            } else if let Some(lexer) = self.lexer_stack.last_mut() {
                lexer.put_back(token);
            }
        }
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
        let is_angled = matches!(token.kind, PPTokenKind::Less);
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

        // Check for built-in headers first for angled includes
        let include_source_id = if is_angled {
            if let Some(content) = self.built_in_headers.get(path_str.as_str()) {
                self.source_manager.add_file(&path_str, content)
            } else {
                // Get current directory
                let current_file_id = self.lexer_stack.last().unwrap().source_id;
                let current_file_info = self.source_manager.get_file_info(current_file_id).unwrap();
                let current_dir = current_file_info.path.parent().unwrap_or(Path::new("."));

                // Resolve the path
                let resolved_path = self.header_search.resolve_path(&path_str, is_angled, current_dir);
                let resolved_path = if let Some(path) = resolved_path {
                    path
                } else {
                    // For angled includes, if not found, emit warning and skip
                    let diag = crate::diagnostic::Diagnostic {
                        level: crate::diagnostic::DiagnosticLevel::Warning,
                        message: format!("Include file '{}' not found, skipping", path_str),
                        location: SourceSpan::new(token.location, token.location),
                        code: Some("include_file_not_found".to_string()),
                        hints: vec!["Check the include path and ensure the file exists".to_string()],
                        related: Vec::new(),
                    };
                    self.diag.report_diagnostic(diag);
                    return Ok(());
                };

                // Load the file
                self.source_manager
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
                    })?
            }
        } else {
            // For quoted includes, resolve as before
            let current_file_id = self.lexer_stack.last().unwrap().source_id;
            let current_file_info = self.source_manager.get_file_info(current_file_id).unwrap();
            let current_dir = current_file_info.path.parent().unwrap_or(Path::new("."));

            // Resolve the path
            let resolved_path = self.header_search.resolve_path(&path_str, is_angled, current_dir);
            let resolved_path = if let Some(path) = resolved_path {
                path
            } else {
                return Err(PreprocessorError::FileNotFound);
            };

            // Load the file
            self.source_manager
                .add_file_from_path(&resolved_path)
                .map_err(|_| PreprocessorError::FileNotFound)?
        };

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
            found_non_skipping: condition, // Set to true if condition is true
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
            found_non_skipping: defined,
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
            found_non_skipping: !defined,
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
        // Collect tokens until end of line
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
            return Err(PreprocessorError::InvalidLineDirective);
        }

        // Expand macros in tokens
        self.expand_tokens(&mut tokens)?;

        if tokens.is_empty() {
            return Err(PreprocessorError::InvalidLineDirective);
        }

        // Parse line number
        let logical_line = match &tokens[0].kind {
            PPTokenKind::Number(symbol) => {
                let text = symbol.as_str();
                text.parse::<u32>()
                    .map_err(|_| PreprocessorError::InvalidLineDirective)?
            }
            _ => return Err(PreprocessorError::InvalidLineDirective),
        };

        // Validate line number (should be positive)
        if logical_line == 0 {
            return Err(PreprocessorError::InvalidLineDirective);
        }

        // Optional filename
        let logical_file = if tokens.len() > 1 {
            match &tokens[1].kind {
                PPTokenKind::StringLiteral(symbol) => {
                    let full_str = symbol.as_str();
                    if full_str.starts_with('"') && full_str.ends_with('"') {
                        Some(full_str[1..full_str.len() - 1].to_string())
                    } else {
                        return Err(PreprocessorError::InvalidLineDirective);
                    }
                }
                _ => return Err(PreprocessorError::InvalidLineDirective), // Extra tokens that aren't filename
            }
        } else {
            None
        };

        // Check for too many tokens
        if tokens.len() > 2 {
            return Err(PreprocessorError::InvalidLineDirective);
        }

        // Get current physical line (where #line directive appears)
        let physical_line = start_line;

        // The #line directive sets the line number for the following line,
        // so we need to adjust the logical_line for the entry
        let entry_logical_line = logical_line - 1;

        // Add entry to LineMap
        if let Some(lexer) = self.lexer_stack.last() {
            if let Some(line_map) = self.source_manager.get_line_map_mut(lexer.source_id) {
                let entry = crate::source_manager::LineDirective::new(physical_line, entry_logical_line, logical_file);
                line_map.add_entry(entry);
            }
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
        if self.is_currently_skipping() {
            // Skip to end of line
            let directive_line = if let Some(lexer) = self.lexer_stack.last() {
                lexer.get_current_line()
            } else {
                0
            };
            while let Some(token) = self.lex_token() {
                if let Some(lexer) = self.lexer_stack.last() {
                    let token_line = lexer.get_line(token.location.0);
                    if token_line != directive_line {
                        // Put back the token from the next line
                        if let Some(lexer) = self.lexer_stack.last_mut() {
                            lexer.put_back(token);
                        }
                        break;
                    }
                }
            }
            return Ok(());
        }
        // Collect the error message from the rest of the line
        let mut message_parts = Vec::new();
        // Get the location of the #error directive
        let directive_location = if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
        } else {
            SourceLoc(0)
        };
        let directive_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };
        while let Some(token) = self.lex_token() {
            if let Some(lexer) = self.lexer_stack.last() {
                let token_line = lexer.get_line(token.location.0);
                if token_line != directive_line {
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
        let diag = crate::diagnostic::Diagnostic {
            level: crate::diagnostic::DiagnosticLevel::Error,
            message: format!("#error directive: {}", message),
            location: SourceSpan::new(directive_location, directive_location),
            code: Some("error_directive".to_string()),
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diag.report_diagnostic(diag);
        Err(PreprocessorError::ErrorDirective(message))
    }

    fn handle_warning(&mut self) -> Result<(), PreprocessorError> {
        // Collect the warning message from the rest of the line
        let mut message_parts = Vec::new();
        let directive_location = if let Some(lexer) = self.lexer_stack.last() {
            SourceLoc::new(lexer.source_id, lexer.position)
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
            result.push_str(&token.get_text());
        }
        result
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &Symbol,
        _token: &PPToken,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // For Level B: Create a virtual buffer containing the replacement text
        let replacement_text = self.tokens_to_string(&macro_info.tokens);
        let virtual_buffer = replacement_text.into_bytes();
        let virtual_id = self.source_manager.add_virtual_buffer(virtual_buffer, &format!("macro_{}", symbol.as_str()));

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
        symbol: &Symbol,
        _token: &PPToken,
    ) -> Result<Vec<PPToken>, PreprocessorError> {
        // Parse arguments from lexer
        let args = self.parse_macro_args_from_lexer(macro_info)?;

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args)?;

        // For Level B: Create a virtual buffer containing the substituted text
        let replacement_text = self.tokens_to_string(&substituted);
        let virtual_buffer = replacement_text.into_bytes();
        let virtual_id = self.source_manager.add_virtual_buffer(virtual_buffer, &format!("macro_{}", symbol.as_str()));

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
                        let right_token = &macro_info.tokens[i + 1];

                        // Substitute the right token if it's a parameter
                        let right_substituted =
                            if let PPTokenKind::Identifier(symbol) = right_token.kind {
                                if let Some(param_index) =
                                    macro_info.parameter_list.iter().position(|&p| p == symbol)
                                {
                                    args[param_index].clone()
                                } else if macro_info.variadic_arg == Some(symbol) {
                                    let start_index = macro_info.parameter_list.len();
                                    args.iter().skip(start_index).flatten().cloned().collect()
                                } else {
                                    vec![right_token.clone()]
                                }
                            } else {
                                vec![right_token.clone()]
                            };

                        // Paste with the first token of right_substituted
                        if let Some(right) = right_substituted.first() {
                            let pasted = self.paste_tokens(&left, right)?;
                            result.extend(pasted);
                        }
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

        Ok(PPToken::new(
            PPTokenKind::StringLiteral(Symbol::new(&result)),
            PPTokenFlags::empty(),
            location,
            result.len() as u16,
        ))
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

        Ok(vec![PPToken::new(
            PPTokenKind::Identifier(symbol),
            PPTokenFlags::empty(),
            left.location, // Use left token's location
            pasted_text.len() as u16,
        )])
    }

    /// Expand tokens by rescanning for further macro expansion
    fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>) -> Result<(), PreprocessorError> {
        let mut i = 0;
        while i < tokens.len() {
            let token = &tokens[i];
            if let PPTokenKind::Identifier(symbol) = &token.kind {
                if symbol.as_str() == "__LINE__" {
                    let line = if let Some(presumed) = self.source_manager.get_presumed_location(token.location) {
                        presumed.0
                    } else {
                        1
                    };
                    let line_str = line.to_string();
                    let line_symbol = Symbol::new(&line_str);
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
            }
            let symbol = match tokens[i].kind {
                PPTokenKind::Identifier(s) => s,
                _ => {
                    i += 1;
                    continue;
                }
            };
            if let Some(macro_info) = self.macros.get(&symbol).cloned() {
                if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE)
                    && !macro_info.flags.contains(MacroFlags::DISABLED)
                {
                    if i + 1 < tokens.len() && tokens[i + 1].kind == PPTokenKind::LeftParen {
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
                                        current_arg.push(tokens[k].clone());
                                    }
                                    PPTokenKind::RightParen => {
                                        paren_depth -= 1;
                                        current_arg.push(tokens[k].clone());
                                    }
                                    PPTokenKind::Comma if paren_depth == 0 => {
                                        args.push(current_arg);
                                        current_arg = Vec::new();
                                    }
                                    _ => {
                                        current_arg.push(tokens[k].clone());
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
                                return Err(PreprocessorError::InvalidMacroParameter);
                            }
                            // Substitute
                            let substituted = self.substitute_macro(&macro_info, &args)?;
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
                            self.expand_tokens(tokens)?;
                            // Re-enable
                            if let Some(m) = self.macros.get_mut(&symbol) {
                                m.flags.remove(MacroFlags::DISABLED);
                            }
                            continue;
                        }
                    }
                }
            }
            // For object macros
            if let Some(expanded) = self.expand_macro(&tokens[i])? {
                tokens.splice(i..i + 1, expanded);
                continue;
            }
            i += 1;
        }
        Ok(())
    }
}
