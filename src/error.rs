use crate::{
    codegen::error::CodegenError, parser::error::ParserError,
    preprocessor::error::PreprocessorError,
};

use thiserror::Error;

/// The main error type for the application.
#[derive(Debug, Error)]
pub enum Error {
    /// An error from the preprocessor.
    #[error("{0}")]
    Preprocessor(#[from] PreprocessorError),
    /// An error from the parser.
    #[error("{0}")]
    Parser(#[from] ParserError),
    /// An error from the code generator.
    #[error("{0}")]
    Codegen(#[from] CodegenError),
}

/// Represents a report of an error.
#[derive(Debug, Clone)]
pub struct Report {
    /// The error message.
    msg: String,
    /// The path of the file where the error occurred.
    path: Option<String>,
    /// The location (line and column) of the error.
    loc: Option<(usize, usize)>,
}

impl Report {
    /// Creates a new `Report`.
    ///
    /// # Arguments
    ///
    /// * `msg` - The error message.
    /// * `path` - The path of the file where the error occurred.
    /// * `loc` - The location (line and column) of the error.
    ///
    /// # Returns
    ///
    /// A new `Report` instance.
    pub fn new(msg: String, path: Option<String>, loc: Option<(usize, usize)>) -> Self {
        Self { msg, path, loc }
    }
}

/// Prints a formatted error report to stderr.
///
/// # Arguments
///
/// * `report` - The report to print.
pub fn report(report: &Report) {
    eprintln!("\x1b[31mError\x1b[0m: {}", report.msg);
    if let Some(path) = &report.path {
        if let Some((line, col)) = report.loc {
            eprintln!(" --> {}:{}:{}", path, line, col);
        } else {
            eprintln!(" --> {}", path);
        }
    }
}
