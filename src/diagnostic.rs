use crate::lexer::TokenKind;
use crate::source_manager::{SourceManager, SourceSpan};
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

    #[error("Invalid integer constant: {text}")]
    InvalidIntegerConstant { text: String, location: SourceSpan },

    #[error("Invalid float constant: {text}")]
    InvalidFloatConstant { text: String, location: SourceSpan },

}

impl ParseError {
    pub fn location(&self) -> SourceSpan {
        match self {
            ParseError::UnexpectedToken { location, .. } => *location,
            ParseError::UnexpectedEof { location } => *location,
            ParseError::SyntaxError { location, .. } => *location,
            ParseError::InvalidIntegerConstant { location, .. } => *location,
            ParseError::InvalidFloatConstant { location, .. } => *location,
        }
    }
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

    pub fn report_error(&mut self, error: SemanticError) {
        let diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message: error.to_string(),
            location: error.location(),
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diagnostics.push(diag);
    }

    pub fn report_warning(&mut self, warning: SemanticWarning) {
        if self.disable_all_warnings {
            return;
        }

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
        let level = if self.warnings_as_errors {
            DiagnosticLevel::Error
        } else {
            DiagnosticLevel::Warning
        };
        let diag = Diagnostic {
            level,
            message,
            location,
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diagnostics.push(diag);
    }

    pub fn report_parse_error(&mut self, error: ParseError) {
        let diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message: error.to_string(),
            location: error.location(),
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diagnostics.push(diag);
    }

    pub fn report_note(&mut self, message: String, location: SourceSpan) {
        let diag = Diagnostic {
            level: DiagnosticLevel::Note,
            message,
            location,
            code: None,
            hints: Vec::new(),
            related: Vec::new(),
        };
        self.diagnostics.push(diag);
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
    #[error("Incomplete type '{name}'")]
    IncompleteType { name: Symbol, location: SourceSpan },
    #[error("Invalid operand: {operation}")]
    InvalidOperand { operation: String, location: SourceSpan },
    #[error("Not lvalue: {operation}")]
    NotLValue { operation: String, location: SourceSpan },

    // Semantic lowering errors
    #[error("Duplicate storage class specifier")]
    DuplicateStorageClass,
    #[error("Illegal storage class with typedef")]
    IllegalTypedefStorage,
    #[error("Missing base type in declaration")]
    MissingBaseType,
    #[error("Invalid type combination")]
    InvalidTypeCombination,
    #[error("{message}")]
    InvalidDeclarator { message: String, location: SourceSpan },
    #[error("Unsupported feature: {feature}")]
    UnsupportedFeature { feature: String, location: SourceSpan },

    // Binary operation errors
    #[error("{message}")]
    InvalidBinaryOp { message: String, location: SourceSpan },
}

impl SemanticError {
    pub fn location(&self) -> SourceSpan {
        match self {
            SemanticError::UndeclaredIdentifier { location, .. } => *location,
            SemanticError::Redefinition { second_def, .. } => *second_def,
            SemanticError::TypeMismatch { location, .. } => *location,
            SemanticError::IncompleteType { location, .. } => *location,
            SemanticError::InvalidOperand { location, .. } => *location,
            SemanticError::NotLValue { location, .. } => *location,
            SemanticError::DuplicateStorageClass => SourceSpan::empty(),
            SemanticError::IllegalTypedefStorage => SourceSpan::empty(),
            SemanticError::MissingBaseType => SourceSpan::empty(),
            SemanticError::InvalidTypeCombination => SourceSpan::empty(),
            SemanticError::InvalidDeclarator { location, .. } => *location,
            SemanticError::UnsupportedFeature { location, .. } => *location,
            SemanticError::InvalidBinaryOp { location, .. } => *location,
        }
    }
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
        let level_str = match diag.level {
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
            DiagnosticLevel::Note => "note",
        };

        let mut result = format!("{}: {}", level_str, diag.message);

        // Add source location if available
        if let Some(file_info) = source_manager.get_file_info(diag.location.source_id()) {
            let (line, col, filename) = if let Some((presumed_line, presumed_col, presumed_file)) =
                source_manager.get_presumed_location(diag.location.start)
            {
                (
                    presumed_line,
                    presumed_col,
                    presumed_file.unwrap_or_else(|| file_info.path.to_str().unwrap_or("<invalid>")),
                )
            } else {
                (1, 1, file_info.path.to_str().unwrap_or("<invalid>"))
            };
            result.push_str(&format!(" at {}:{}:{}", filename, line, col));
        }

        // Add hints if enabled
        if self.show_hints && !diag.hints.is_empty() {
            for hint in &diag.hints {
                result.push_str(&format!("\n  hint: {}", hint));
            }
        }

        // Add source code snippet if enabled
        if self.show_source {
            let source_text = source_manager.get_source_text(diag.location);
            result.push_str(&format!("\n  |\n  | {}\n  |", source_text.replace('\n', "\n  | ")));
        }

        result
    }

    /// Format multiple diagnostics
    pub fn format_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) -> String {
        diagnostics
            .iter()
            .map(|diag| self.format_diagnostic(diag, source_manager))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    /// Print a diagnostic directly to stderr
    pub fn print_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) {
        eprintln!("{}", self.format_diagnostic(diag, source_manager));
    }

    /// Print all diagnostics to stderr
    pub fn print_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) {
        for diag in diagnostics {
            self.print_diagnostic(diag, source_manager);
        }
    }
}
