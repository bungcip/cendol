use thiserror::Error;

/// An error that can occur during preprocessing.
#[derive(Error, Debug, PartialEq)]
pub enum PreprocessorError {
    /// An unexpected character was encountered.
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char),
    /// An unexpected directive was encountered.
    #[error("Unexpected directive: {0}")]
    UnexpectedDirective(String),
    /// The end of the input was reached unexpectedly in macro arguments.
    #[error("Unexpected EOF in macro arguments")]
    UnexpectedEofInMacroArgs,
    /// A '##' operator was found at the start of a macro expansion.
    #[error("'##' at start of macro expansion")]
    HashHashAtStartOfMacro,
    /// A '##' operator was found at the end of a macro expansion.
    #[error("'##' at end of macro expansion")]
    HashHashAtEndOfMacro,
    /// An identifier was expected after a #define directive.
    #[error("Expected identifier after #define")]
    ExpectedIdentifierAfterDefine,
    /// The end of the input was reached unexpectedly in macro parameters.
    #[error("Unexpected EOF in macro parameters")]
    UnexpectedEofInMacroParams,
    /// Macro expansion is too deep, possibly due to infinite recursion.
    #[error("Macro expansion too deep, possible infinite recursion")]
    MacroExpansionTooDeep,
    /// A generic error.
    #[error("u: {0}")]
    Generic(String),
    /// An unexpected #elif directive was encountered.
    #[error("Unexpected #elif")]
    UnexpectedElif,
    /// An unexpected #else directive was encountered.
    #[error("Unexpected #else")]
    UnexpectedElse,
    /// An unexpected #endif directive was encountered.
    #[error("Unexpected #endif")]
    UnexpectedEndif,
    /// A conditional directive was not terminated.
    #[error("Unterminated conditional directive")]
    UnterminatedConditional,
    /// A file was not found.
    #[error("File not found: {0}")]
    FileNotFound(String),
    /// An invalid #include directive was encountered.
    #[error("Invalid #include directive")]
    InvalidInclude,
}

impl From<&str> for PreprocessorError {
    fn from(s: &str) -> Self {
        PreprocessorError::Generic(s.to_string())
    }
}

impl From<std::io::Error> for PreprocessorError {
    fn from(err: std::io::Error) -> Self {
        PreprocessorError::Generic(err.to_string())
    }
}
