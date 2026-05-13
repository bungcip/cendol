use crate::diagnostic::{Diagnostic, DiagnosticLevel, IntoDiagnostic};
use crate::parser::TokenKind;
use crate::source_manager::SourceSpan;
use thiserror::Error;

/// Parse errors
#[derive(Debug, Error)]
#[error("{kind}")]
pub(crate) struct ParseError {
    pub(crate) span: SourceSpan,
    pub(crate) kind: ParseErrorKind,
}

/// Parse error kinds
#[derive(Debug, Error)]
pub(crate) enum ParseErrorKind {
    #[error("Unexpected token: expected {expected}, found {found}")]
    UnexpectedToken { expected: &'static str, found: TokenKind },

    #[error("Unexpected End of File")]
    UnexpectedEof,

    #[error("Declaration not allowed in this context")]
    DeclarationNotAllowed,

    #[error("_Atomic(type-name) specifier cannot be used with {0} type ")]
    InvalidAtomicSpec(&'static str),
}

impl IntoDiagnostic for ParseError {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        vec![Diagnostic {
            level: DiagnosticLevel::Error,
            message: self.to_string(),
            span: self.span,
            ..Default::default()
        }]
    }
}
