use crate::diagnostic::{
    DiagDisplay, DiagFormatter, Diagnostic, DiagnosticLevel, IntoDiagnostic, format_diag_without_registry,
};
use crate::parser::TokenKind;
use crate::source_manager::SourceSpan;
use std::fmt::Write;

/// Parse errors
#[derive(Debug)]
pub(crate) struct ParseDiag {
    pub(crate) span: SourceSpan,
    pub(crate) kind: ParseError,
}

impl std::fmt::Display for ParseDiag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = format_diag_without_registry(&self.kind);
        f.write_str(&msg)
    }
}

/// Parse error kinds
#[derive(Debug)]
pub(crate) enum ParseError {
    UnexpectedToken { expected: &'static str, found: TokenKind },
    UnexpectedEof,
    DeclarationNotAllowed,
    InvalidAtomicSpec(&'static str),
}

// impl std::fmt::Display for ParseError {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let msg = format_diag_without_registry(self);
//         f.write_str(&msg)
//     }
// }

impl DiagDisplay for ParseError {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedToken { expected, found } => {
                write!(f, "Unexpected token: expected {}, found {}", expected, found)
            }
            ParseError::UnexpectedEof => {
                write!(f, "Unexpected End of File")
            }
            ParseError::DeclarationNotAllowed => {
                write!(f, "Declaration not allowed in this context")
            }
            ParseError::InvalidAtomicSpec(type_kind) => {
                write!(
                    f,
                    "_Atomic(type-name) specifier cannot be used with {} type ",
                    type_kind
                )
            }
        }
    }
}

impl DiagDisplay for ParseDiag {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl IntoDiagnostic for ParseDiag {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        vec![Diagnostic {
            level: DiagnosticLevel::Error,
            message: format_diag_without_registry(&self),
            span: self.span,
            ..Default::default()
        }]
    }
}
