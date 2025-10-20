use crate::{
    codegen::error::CodegenError, parser::error::ParserError,
    preprocessor::error::PreprocessorError,
};
use ariadne::{Color, Fmt, Label, Report as AriadneReport, ReportKind, Source};
use thiserror::Error;

/// A custom span type for `ariadne`.
pub type Span = (String, std::ops::Range<usize>);

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
    let path = report.path.clone().unwrap_or_else(|| "input".to_string());
    let msg = report.msg.clone();

    if let Some((line, col)) = report.loc {
        let source = std::fs::read_to_string(&path).unwrap_or_else(|_| "".to_string());
        let offset = source
            .lines()
            .take(line - 1)
            .map(|line| line.len() + 1)
            .sum::<usize>()
            + col
            - 1;

        AriadneReport::<'static, Span>::build(ReportKind::Error, path.clone(), offset)
            .with_code(3)
            .with_message(&msg)
            .with_label(
                Label::new((path.clone(), offset..offset + 1))
                    .with_message(msg.fg(Color::Red))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((path.clone(), Source::from(source)))
            .unwrap();
    } else {
        AriadneReport::<'static, Span>::build(ReportKind::Error, path.clone(), 0)
            .with_code(3)
            .with_message(msg)
            .with_label(
                Label::new((path.clone(), 0..0))
                    .with_message("".fg(Color::Red))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((path, Source::from("")))
            .unwrap();
    }
}
