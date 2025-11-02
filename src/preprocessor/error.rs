use crate::SourceSpan;
use thiserror::Error;

/// An error that can occur during preprocessing.
#[derive(Error, Debug, PartialEq)]
pub enum PreprocessorError {
    /// An unexpected character was encountered.
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char, Option<SourceSpan>),
    /// An unexpected directive was encountered.
    #[error("Unexpected directive: {0}")]
    UnexpectedDirective(String, Option<SourceSpan>),
    /// An unknown directive was encountered.
    #[error("Unknown directive: {0}")]
    UnknownDirective(String, Option<SourceSpan>),
    /// The end of the input was reached unexpectedly in macro arguments.
    #[error("Unexpected EOF in macro arguments")]
    UnexpectedEofInMacroArgs(Option<SourceSpan>),
    /// A '##' operator was found at the start of a macro expansion.
    #[error("'##' at start of macro expansion")]
    HashHashAtStartOfMacro(Option<SourceSpan>),
    /// A '##' operator was found at the end of a macro expansion.
    #[error("'##' at end of macro expansion")]
    HashHashAtEndOfMacro(Option<SourceSpan>),
    /// An identifier was expected after a #define directive.
    #[error("Expected identifier after #define")]
    ExpectedIdentifierAfterDefine(Option<SourceSpan>),
    /// The end of the input was reached unexpectedly in macro parameters.
    #[error("Unexpected EOF in macro parameters")]
    UnexpectedEofInMacroParams(Option<SourceSpan>),
    /// Macro expansion is too deep, possibly due to infinite recursion.
    #[error("Macro expansion too deep, possible infinite recursion")]
    MacroExpansionTooDeep(Option<SourceSpan>),
    /// A generic error.
    #[error("{0}")]
    Generic(String, Option<SourceSpan>),
    /// An unexpected #elif directive was encountered.
    #[error("Unexpected #elif")]
    UnexpectedElif(Option<SourceSpan>),
    /// An unexpected #else directive was encountered.
    #[error("Unexpected #else")]
    UnexpectedElse(Option<SourceSpan>),
    /// An unexpected #endif directive was encountered.
    #[error("Unexpected #endif")]
    UnexpectedEndif(Option<SourceSpan>),
    /// A conditional directive was not terminated.
    #[error("Unterminated conditional directive")]
    UnterminatedConditional(Option<SourceSpan>),
    /// A file was not found.
    #[error("File not found: {0}")]
    FileNotFound(String, Option<SourceSpan>),
    /// An invalid #include directive was encountered.
    #[error("Invalid #include directive")]
    InvalidInclude(Option<SourceSpan>),
}

impl From<&str> for PreprocessorError {
    fn from(s: &str) -> Self {
        PreprocessorError::Generic(s.to_string(), None)
    }
}

impl From<std::io::Error> for PreprocessorError {
    fn from(err: std::io::Error) -> Self {
        PreprocessorError::Generic(err.to_string(), None)
    }
}

impl PreprocessorError {
    /// Extracts the span from the error if available.
    pub fn span(&self) -> Option<SourceSpan> {
        match self {
            PreprocessorError::UnexpectedChar(_, span) => *span,
            PreprocessorError::UnexpectedDirective(_, span) => *span,
            PreprocessorError::UnknownDirective(_, span) => *span,
            PreprocessorError::UnexpectedEofInMacroArgs(span) => *span,
            PreprocessorError::HashHashAtStartOfMacro(span) => *span,
            PreprocessorError::HashHashAtEndOfMacro(span) => *span,
            PreprocessorError::ExpectedIdentifierAfterDefine(span) => *span,
            PreprocessorError::UnexpectedEofInMacroParams(span) => *span,
            PreprocessorError::MacroExpansionTooDeep(span) => *span,
            PreprocessorError::Generic(_, span) => *span,
            PreprocessorError::UnexpectedElif(span) => *span,
            PreprocessorError::UnexpectedElse(span) => *span,
            PreprocessorError::UnexpectedEndif(span) => *span,
            PreprocessorError::UnterminatedConditional(span) => *span,
            PreprocessorError::FileNotFound(_, span) => *span,
            PreprocessorError::InvalidInclude(span) => *span,
        }
    }
}
