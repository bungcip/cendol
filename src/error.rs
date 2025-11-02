use crate::{
    codegen::error::CodegenError,
    file::{FileId, FileManager},
    parser::error::ParserError,
    preprocessor::error::PreprocessorError,
    semantic::error::SemanticError,
};
use ariadne::{Color, Config, Fmt, Label, Report as AriadneReport, ReportKind, Source, Span};
use thiserror::Error;

/// Returns `true` if colors should be used for the report.
fn colors_enabled() -> bool {
    use atty::Stream;

    // Honor `NO_COLOR` environment variable.
    // See: https://no-color.org/
    std::env::var("NO_COLOR").is_err() && atty::is(Stream::Stderr)
}

/// implement trait neccesary for ariadne
struct DiagnosticSpan(String, SourceSpan);
impl Span for DiagnosticSpan {
    type SourceId = String;

    fn source(&self) -> &Self::SourceId {
        &self.0
    }

    fn start(&self) -> usize {
        self.1.start_offset() as usize
    }

    fn end(&self) -> usize {
        self.1.end_offset() as usize
    }
}

/// The main error type for the application.
#[derive(Debug, Error)]
pub enum Error {
    /// An error from the preprocessor.
    #[error("{0}")]
    Preprocessor(#[from] PreprocessorError),

    /// An error from the parser.
    #[error("{0}")]
    Parser(#[from] ParserError),

    /// An error from semantic analyzer
    #[error("{0}")]
    Semantic(#[from] SemanticError),

    /// An error from the code generator.
    #[error("{0}")]
    Codegen(#[from] CodegenError),
}

use crate::SourceSpan;
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
pub fn report(report: &Report, fm: &FileManager) {
    let path = report.path.clone().unwrap_or_else(|| "input".to_string());
    let msg = &report.msg;
    let kind = if report.is_warning {
        // msg = format!("warning: {}", msg);
        ReportKind::Warning
    } else {
        ReportKind::Error
    };

    let config = Config::default().with_color(colors_enabled());

    let code;
    let start_offset;
    let source;

    let diag_span = if let Some(span) = &report.span {
        source = fm.read(span.file_id()).unwrap_or("").to_string();
        start_offset = span.start_offset() as usize;
        code = 3;
        DiagnosticSpan(path.clone(), *span)
    } else {
        code = 3;
        start_offset = 0;
        source = "".to_string();
        DiagnosticSpan(path.clone(), SourceSpan::default())
    };

    AriadneReport::build(kind, &path, start_offset)
        .with_code(code)
        .with_message(msg)
        .with_config(config)
        .with_label(
            Label::new(diag_span)
                .with_message(msg.fg(Color::Red))
                .with_color(Color::Red),
        )
        .finish()
        .eprint((path.clone(), Source::from(source)))
        .unwrap();
}
