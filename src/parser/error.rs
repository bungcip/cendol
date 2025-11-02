use crate::SourceSpan;
use crate::parser::token::Token;
use serde::de::Unexpected;
use thiserror::Error;

/// An error that can occur during parsing.
#[derive(Error, Debug)]
pub enum ParserError {
    /// An unexpected token was encountered.
    #[error("Unexpected token: {0}")]
    UnexpectedToken(Token),
    /// The end of the input was reached unexpectedly.
    #[error("Unexpected end of input")]
    UnexpectedEof(SourceSpan),
}

impl ParserError {
    pub fn span(&self) -> SourceSpan {
        match self {
            ParserError::UnexpectedToken(token) => token.span,
            ParserError::UnexpectedEof(span) => *span,
        }
    }
}
