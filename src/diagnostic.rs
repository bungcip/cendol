use crate::source_manager::SourceSpan;
use symbol_table::GlobalSymbol as Symbol;

/// Semantic analysis result
pub struct SemanticOutput {
    pub errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
}

/// Diagnostic engine for collecting and reporting semantic errors and warnings
pub struct DiagnosticEngine {
    pub errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
}

impl DiagnosticEngine {
    pub fn new() -> Self {
        DiagnosticEngine {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn report_error(&mut self, error: SemanticError) {
        self.errors.push(error);
    }

    pub fn report_warning(&mut self, warning: SemanticWarning) {
        self.warnings.push(warning);
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    pub fn warning_count(&self) -> usize {
        self.warnings.len()
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
        second_def: SourceSpan
    },
    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        location: SourceSpan
    },
    #[error("Incomplete type '{name}'")]
    IncompleteType { name: Symbol, location: SourceSpan },
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
        location: SourceSpan
    },
    #[error("Unreachable code")]
    UnreachableCode { location: SourceSpan },
}