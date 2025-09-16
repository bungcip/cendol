use thiserror::Error;
use crate::preprocessor::token::Token;

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Unexpected token: {0:?}")]
    UnexpectedToken(Token),
    #[error("Unexpected end of input")]
    UnexpectedEof,
}
