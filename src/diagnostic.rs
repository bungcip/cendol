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

    #[error("Invalid declarator")]
    InvalidDeclarator { location: SourceSpan },
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
        let (message, location) = match error {
            SemanticError::UndeclaredIdentifier { name, location } => {
                (format!("Undeclared identifier '{}'", name), location)
            }
            SemanticError::Redefinition {
                name,
                first_def: _first_def,
                second_def,
            } => (format!("Redefinition of '{}'", name), second_def),
            SemanticError::TypeMismatch {
                expected,
                found,
                location,
            } => (
                format!("Type mismatch: expected {}, found {}", expected, found),
                location,
            ),
            SemanticError::IncompleteType { name, location } => (format!("Incomplete type '{}'", name), location),
            SemanticError::InvalidOperand { operation, location } => {
                (format!("Invalid operand: {}", operation), location)
            }
            SemanticError::NotLValue { operation, location } => (operation.to_string(), location),

            // Semantic lowering errors
            SemanticError::DuplicateStorageClass => {
                ("Duplicate storage class specifier".to_string(), SourceSpan::empty())
            }
            SemanticError::IllegalTypedefStorage => {
                ("Illegal storage class with typedef".to_string(), SourceSpan::empty())
            }
            SemanticError::MissingBaseType => ("Missing base type in declaration".to_string(), SourceSpan::empty()),
            SemanticError::InvalidTypeCombination => ("Invalid type combination".to_string(), SourceSpan::empty()),
            SemanticError::InvalidFunctionDeclarator { location } => {
                ("Invalid function declarator".to_string(), location)
            }
            SemanticError::InvalidDeclarator { location } => ("Invalid declarator".to_string(), location),
            SemanticError::UnsupportedFeature { feature, location } => {
                (format!("Unsupported feature: {}", feature), location)
            }

            // Binary operation errors
            SemanticError::InvalidBinaryOperation { operation, location } => {
                (format!("Invalid binary operation: {}", operation), location)
            }
            SemanticError::DivisionByZero { location } => ("Division by zero".to_string(), location),
            SemanticError::ModuloByZero { location } => ("Modulo by zero".to_string(), location),
            SemanticError::InvalidShiftAmount { location } => {
                ("Left shift amount is negative or too large".to_string(), location)
            }
            SemanticError::InvalidLogicalOperands { location } => {
                ("Invalid operands for logical operation".to_string(), location)
            }
            SemanticError::IncompleteTypeForBinaryOp { location } => (
                "Cannot perform binary operation on incomplete types".to_string(),
                location,
            ),
            SemanticError::InvalidTypeConversion {
                from_type,
                to_type,
                location,
            } => (
                format!("Invalid type conversion: cannot convert {} to {}", from_type, to_type),
                location,
            ),
            SemanticError::UnsupportedConversion {
                left_type,
                right_type,
                location,
            } => (
                format!("Unsupported conversion between types {} and {}", left_type, right_type),
                location,
            ),
            SemanticError::ConversionOverflow {
                from_type,
                to_type,
                location,
            } => (
                format!("Integer overflow during conversion from {} to {}", from_type, to_type),
                location,
            ),
            SemanticError::InvalidBinaryOperandTypes {
                left_type,
                right_type,
                location,
            } => (
                format!(
                    "Invalid operands for binary operation: {} and {}",
                    left_type, right_type
                ),
                location,
            ),
        };
        let diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message,
            location,
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
            ParseError::InvalidIntegerConstant { text, location } => {
                (format!("Invalid integer constant: {}", text), location)
            }
            ParseError::InvalidFloatConstant { text, location } => {
                (format!("Invalid float constant: {}", text), location)
            }
            ParseError::InvalidDeclarator { location } => ("Invalid declarator".to_string(), location),
        };
        let diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message,
            location,
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
    #[error("Invalid function declarator")]
    InvalidFunctionDeclarator { location: SourceSpan },
    #[error("Invalid declarator")]
    InvalidDeclarator { location: SourceSpan },
    #[error("Unsupported feature: {feature}")]
    UnsupportedFeature { feature: String, location: SourceSpan },

    // Binary operation errors
    #[error("Invalid binary operation: {operation}")]
    InvalidBinaryOperation { operation: String, location: SourceSpan },
    #[error("Division by zero")]
    DivisionByZero { location: SourceSpan },
    #[error("Modulo by zero")]
    ModuloByZero { location: SourceSpan },
    #[error("Left shift amount is negative or too large")]
    InvalidShiftAmount { location: SourceSpan },
    #[error("Invalid operands for logical operation")]
    InvalidLogicalOperands { location: SourceSpan },
    #[error("Cannot perform binary operation on incomplete types")]
    IncompleteTypeForBinaryOp { location: SourceSpan },
    #[error("Invalid type conversion: cannot convert {from_type} to {to_type}")]
    InvalidTypeConversion {
        from_type: String,
        to_type: String,
        location: SourceSpan,
    },
    #[error("Unsupported conversion between types {left_type} and {right_type}")]
    UnsupportedConversion {
        left_type: String,
        right_type: String,
        location: SourceSpan,
    },
    #[error("Integer overflow during conversion from {from_type} to {to_type}")]
    ConversionOverflow {
        from_type: String,
        to_type: String,
        location: SourceSpan,
    },
    #[error("Invalid operands for binary operation: {left_type} and {right_type}")]
    InvalidBinaryOperandTypes {
        left_type: String,
        right_type: String,
        location: SourceSpan,
    },
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
