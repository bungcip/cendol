use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::source_manager::SourceSpan;

/// Preprocessor errors
#[derive(Debug, thiserror::Error)]
pub enum PPErrorKind {
    #[error("File not found: {path}")]
    FileNotFound { path: String },
    #[error("Include depth exceeded")]
    IncludeDepthExceeded,
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
    #[error("Invalid token pasting")]
    InvalidTokenPasting,
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
    #[error("Macro '{name}' redefined with different value")]
    MacroRedefined { name: String },
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
