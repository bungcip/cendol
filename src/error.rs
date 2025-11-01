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

use crate::common::SourceSpan;
use serde::Serialize;

/// Represents a report of an error.
#[derive(Debug, Clone, Serialize)]
pub struct Report {
    /// The error message.
    pub msg: String,
    /// The path of the file where the error occurred.
    pub path: Option<String>,
    /// The span of the error.
    pub span: Option<SourceSpan>,
    /// Whether to print verbose output.
    pub verbose: bool,
    /// Whether the report is a warning.
    pub is_warning: bool,
}

impl std::fmt::Display for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for Report {}

impl Report {
    /// Creates a new `Report`.
    ///
    /// # Arguments
    ///
    /// * `msg` - The error message.
    /// * `path` - The path of the file where the error occurred.
    /// * `span` - The span of the error.
    ///
    /// # Returns
    ///
    /// A new `Report` instance.
    pub fn new(
        msg: String,
        path: Option<String>,
        span: Option<SourceSpan>,
        verbose: bool,
        is_warning: bool,
    ) -> Self {
        Self {
            msg,
            path,
            span,
            verbose,
            is_warning,
        }
    }
}

/// Prints a formatted error report to stderr.
///
/// # Arguments
///
/// * `report` - The report to print.
pub fn report(report: &Report) {
    let path = report.path.clone().unwrap_or_else(|| "input".to_string());
    let mut msg = report.msg.clone();
    let kind = if report.is_warning {
        msg = format!("warning: {}", msg);
        ReportKind::Warning
    } else {
        ReportKind::Error
    };

    if let Some(span) = &report.span {
        let source = std::fs::read_to_string(&path).unwrap_or_else(|_| "".to_string());
        let start_offset = if span.start_line == 0 || span.start_column == 0 {
            0
        } else {
            source
                .lines()
                .take(span.start_line as usize - 1)
                .map(|line| line.len() + 1)
                .sum::<usize>()
                + span.start_column as usize
                - 1
        };
        let end_offset = if span.end_line == 0 || span.end_column == 0 {
            start_offset + 1
        } else {
            source
                .lines()
                .take(span.end_line as usize - 1)
                .map(|line| line.len() + 1)
                .sum::<usize>()
                + span.end_column as usize
                - 1
        };

        AriadneReport::<'static, Span>::build(kind, path.clone(), start_offset)
            .with_code(3)
            .with_message(&msg)
            .with_label(
                Label::new((path.clone(), start_offset..end_offset))
                    .with_message(msg.fg(Color::Red))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((path.clone(), Source::from(source)))
            .unwrap();
    } else {
        AriadneReport::<'static, Span>::build(kind, path.clone(), 0)
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
