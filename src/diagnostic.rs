use crate::lexer::TokenKind;
use crate::source_manager::{SourceManager, SourceSpan};
use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};
use symbol_table::GlobalSymbol as Symbol;

/// Diagnostic severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Note,
}

/// Individual diagnostic with rich context
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub location: SourceSpan,
    pub code: Option<String>,     // Error code like "E001"
    pub hints: Vec<String>,       // Suggestions for fixing
    pub related: Vec<SourceSpan>, // Related locations
}

/// Parse errors
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("Unexpected token: expected {expected_tokens}, found {found:?}")]
    UnexpectedToken {
        expected_tokens: String,
        found: TokenKind,
        location: SourceSpan,
    },

    #[error("Unexpected End of File")]
    UnexpectedEof { location: SourceSpan },

    #[error("Syntax error: {message}")]
    SyntaxError { message: String, location: SourceSpan },

    #[error("Invalid numeric constant: {text}")]
    InvalidNumericConstant { text: String, location: SourceSpan },
}

/// Diagnostic engine for collecting and reporting semantic errors and warnings
pub struct DiagnosticEngine {
    pub diagnostics: Vec<Diagnostic>,
    pub warnings_as_errors: bool,
    pub disable_all_warnings: bool,
}

impl Default for DiagnosticEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl DiagnosticEngine {
    pub fn new() -> Self {
        DiagnosticEngine {
            diagnostics: Vec::new(),
            warnings_as_errors: false,
            disable_all_warnings: false,
        }
    }

    pub fn from_warnings(warnings: &[String]) -> Self {
        let warnings_as_errors = warnings.iter().any(|w| w == "error");
        let disable_all_warnings = warnings.iter().any(|w| w == "no-warnings");
        Self {
            diagnostics: Vec::new(),
            warnings_as_errors,
            disable_all_warnings,
        }
    }

    fn _report(&mut self, level: DiagnosticLevel, message: String, location: SourceSpan) {
        if level == DiagnosticLevel::Warning && self.disable_all_warnings {
            return;
        }

        let final_level = if level == DiagnosticLevel::Warning && self.warnings_as_errors {
            DiagnosticLevel::Error
        } else {
            level
        };

        self.diagnostics.push(Diagnostic {
            level: final_level,
            message,
            location,
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        });
    }

    pub fn report_error(&mut self, error: SemanticError) {
        match error {
            SemanticError::UndeclaredIdentifier { name, location } => {
                let message = format!("Undeclared identifier '{}'", name);
                self._report(DiagnosticLevel::Error, message, location);
            }
            SemanticError::Redefinition {
                name,
                first_def,
                second_def,
            } => {
                // Report the redefinition error with Clang-style location format
                let error_message = format!("redefinition of '{}'", name);
                self._report(DiagnosticLevel::Error, error_message, second_def);

                // Report a note showing the previous definition
                let note_message = "previous definition is here".to_string();
                self._report(DiagnosticLevel::Note, note_message, first_def);
            }
            SemanticError::TypeMismatch {
                expected,
                found,
                location,
            } => (
                format!("Type mismatch: expected {}, found {}", expected, found),
                location,
            ),
            SemanticError::NotAnLvalue { location } => ("Expression is not assignable".to_string(), location),
            SemanticError::InvalidBinaryOperands {
                left_ty,
                right_ty,
                location,
            } => (
                format!(
                    "Invalid operands for binary operation: have '{}' and '{}'",
                    left_ty, right_ty
                ),
                location,
            ),
            SemanticError::NonConstantInitializer { location } => {
                ("Initializer element is not a compile-time constant".to_string(), location)
            }
            SemanticError::InvalidUseOfVoid { location } => {
                ("Invalid use of void type in expression".to_string(), location)
            }
            SemanticError::UnsupportedFeature { feature, location } => {
                let message = format!("Unsupported feature: {}", feature);
                self._report(DiagnosticLevel::Error, message, location);
            }
        }
    }

    pub fn report_warning(&mut self, warning: SemanticWarning) {
        let (message, location) = match warning {
            SemanticWarning::UnusedDeclaration { name, location } => {
                (format!("Unused declaration '{}'", name), location)
            }
            SemanticWarning::ImplicitConversion {
                from_type,
                to_type,
                location,
            } => (
                format!("Implicit conversion from {} to {}", from_type, to_type),
                location,
            ),
            SemanticWarning::UnreachableCode { location } => ("Unreachable code".to_string(), location),
            SemanticWarning::Redefinition {
                name,
                first_def: _first_def,
                second_def,
            } => (format!("Redefinition of '{}'", name), second_def),
        };
        self._report(DiagnosticLevel::Warning, message, location);
    }

    pub fn report_parse_error(&mut self, error: ParseError) {
        let (message, location) = match error {
            ParseError::UnexpectedToken {
                expected_tokens,
                found,
                location,
            } => (
                format!(
                    "Unexpected token: expected one of {}, found {:?}",
                    expected_tokens, found
                ),
                location,
            ),
            ParseError::UnexpectedEof { location } => ("Unexpected End of File".to_string(), location),
            ParseError::SyntaxError { message, location } => (message, location),
            ParseError::InvalidNumericConstant { text, location } => {
                (format!("Invalid numeric constant: {}", text), location)
            }
        };
        self._report(DiagnosticLevel::Error, message, location);
    }

    pub fn report_note(&mut self, message: String, location: SourceSpan) {
        self._report(DiagnosticLevel::Note, message, location);
    }

    pub fn report_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.level == DiagnosticLevel::Error)
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

/// Semantic errors
#[derive(Debug, thiserror::Error)]
pub enum SemanticError {
    #[error("Undeclared identifier '{name}'")]
    UndeclaredIdentifier { name: Symbol, location: SourceSpan },
    #[error("Redefinition of '{name}'")]
    Redefinition {
        name: Symbol,
        first_def: SourceSpan,
        second_def: SourceSpan,
    },
    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        location: SourceSpan,
    },
    #[error("Expression is not assignable (not an lvalue)")]
    NotAnLvalue { location: SourceSpan },
    #[error("Invalid operands for binary operation: have '{left_ty}' and '{right_ty}'")]
    InvalidBinaryOperands {
        left_ty: String,
        right_ty: String,
        location: SourceSpan,
    },
    #[error("Initializer element is not a compile-time constant")]
    NonConstantInitializer { location: SourceSpan },
    #[error("Invalid use of void type in expression")]
    InvalidUseOfVoid { location: SourceSpan },
    #[error("Unsupported feature: {feature}")]
    UnsupportedFeature { feature: String, location: SourceSpan },
}

/// Semantic warnings
#[derive(Debug, thiserror::Error)]
pub enum SemanticWarning {
    #[error("Unused declaration '{name}'")]
    UnusedDeclaration { name: Symbol, location: SourceSpan },
    #[error("Implicit conversion from {from_type} to {to_type}")]
    ImplicitConversion {
        from_type: String,
        to_type: String,
        location: SourceSpan,
    },
    #[error("Unreachable code")]
    UnreachableCode { location: SourceSpan },
    #[error("Redefinition of '{name}'")]
    Redefinition {
        name: Symbol,
        first_def: SourceSpan,
        second_def: SourceSpan,
    },
}

/// Configurable error formatter using annotate_snippets
pub struct ErrorFormatter {
    pub show_source: bool,
    pub show_hints: bool,
    pub use_colors: bool,
    pub max_context: usize,
}

impl Default for ErrorFormatter {
    fn default() -> Self {
        ErrorFormatter {
            show_source: true,
            show_hints: true,
            use_colors: true,
            max_context: 3,
        }
    }
}

impl ErrorFormatter {
    /// Format a single diagnostic with rich source code context
    pub fn format_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let snippet = self.create_snippet(diag, source_manager);
        let renderer = if self.use_colors {
            Renderer::styled()
        } else {
            Renderer::plain()
        };

        let (_level_str, message) = match diag.level {
            DiagnosticLevel::Error => {
                let location_str = self.format_location(diag, source_manager);
                let full_message = format!("{}: error: {}", location_str, diag.message);
                ("error", full_message)
            }
            DiagnosticLevel::Warning => {
                let location_str = self.format_location(diag, source_manager);
                let full_message = format!("{}: warning: {}", location_str, diag.message);
                ("warning", full_message)
            }
            DiagnosticLevel::Note => {
                let location_str = self.format_location(diag, source_manager);
                let full_message = format!("{}: note: {}", location_str, diag.message);
                ("note", full_message)
            }
        };

        let mut group = self.level(diag).primary_title(&message).element(snippet);

        for hint in &diag.hints {
            group = group.element(Level::HELP.message(hint));
        }

        let report = &[group];
        renderer.render(report).to_string()
    }

    fn format_location(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let path = source_manager
            .get_file_info(diag.location.source_id())
            .map(|fi| fi.path.to_str().unwrap_or("<unknown>"))
            .unwrap_or("<unknown>");

        // Get line and column information
        let source_buffer = source_manager.get_buffer(diag.location.source_id());
        if let Ok(source_str) = std::str::from_utf8(source_buffer) {
            // Calculate line and column from byte offset
            let line = source_str[..diag.location.start.offset() as usize].lines().count() + 1;

            let line_start = source_str[..diag.location.start.offset() as usize]
                .rfind('\n')
                .map(|pos| pos + 1)
                .unwrap_or(0);
            let col = (diag.location.start.offset() as usize - line_start) + 1;

            format!("{}:{}:{}", path, line, col)
        } else {
            path.to_string()
        }
    }

    fn level<'a>(&self, diag: &Diagnostic) -> Level<'a> {
        match diag.level {
            DiagnosticLevel::Error => Level::ERROR,
            DiagnosticLevel::Warning => Level::WARNING,
            DiagnosticLevel::Note => Level::NOTE,
        }
    }

    fn create_snippet<'a>(
        &self,
        diag: &'a Diagnostic,
        source_manager: &'a SourceManager,
    ) -> Snippet<'a, annotate_snippets::Annotation<'a>> {
        let source_buffer = source_manager.get_buffer(diag.location.source_id());
        let source = std::str::from_utf8(source_buffer).unwrap_or("");
        let path = source_manager
            .get_file_info(diag.location.source_id())
            .map(|fi| fi.path.to_str().unwrap_or("<unknown>"))
            .unwrap_or("<unknown>");

        let mut snippet = Snippet::source(source).line_start(1).path(path);

        let annotation_kind = AnnotationKind::Primary;

        snippet = snippet.annotation(
            annotation_kind.span(diag.location.start.offset() as usize..diag.location.end.offset() as usize),
        );

        snippet
    }

    /// Format multiple diagnostics
    pub fn format_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) -> String {
        diagnostics
            .iter()
            .map(|diag| self.format_diagnostic(diag, source_manager))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    /// Print all diagnostics to stderr
    pub fn print_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) {
        for diag in diagnostics {
            let formatted = self.format_diagnostic(diag, source_manager);
            eprintln!("{}", formatted);
        }
    }
}
