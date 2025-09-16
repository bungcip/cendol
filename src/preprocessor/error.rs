use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum PreprocessorError {
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char),
    #[error("Unexpected EOF in macro arguments")]
    UnexpectedEofInMacroArgs,
    #[error("'##' at start of macro expansion")]
    HashHashAtStartOfMacro,
    #[error("'##' at end of macro expansion")]
    HashHashAtEndOfMacro,
    #[error("Expected identifier after #define")]
    ExpectedIdentifierAfterDefine,
    #[error("Unexpected EOF in macro parameters")]
    UnexpectedEofInMacroParams,
    #[error("Macro expansion too deep, possible infinite recursion")]
    MacroExpansionTooDeep,
    #[error("Generic error: {0}")]
    Generic(String),
}

impl From<&str> for PreprocessorError {
    fn from(s: &str) -> Self {
        PreprocessorError::Generic(s.to_string())
    }
}
