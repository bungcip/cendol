use std::path::{Path, PathBuf};

use crate::{
    codegen::error::CodegenError,
    file::{self, FileId, FileManager},
    parser::error::ParserError,
    preprocessor::error::PreprocessorError,
    semantic::error::SemanticError,
};
use ariadne::{
    Cache, Color, Config, Fmt, Label, Report as AriadneReport, ReportKind, Source, Span,
};
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
    pub fn new(msg: String, span: Option<SourceSpan>, verbose: bool, is_warning: bool) -> Self {
        Self {
            msg,
            span,
            verbose,
            is_warning,
        }
    }

    pub fn err(msg: String, span: Option<SourceSpan>) -> Self {
        Self {
            msg,
            span,
            verbose: false,
            is_warning: false,
        }
    }

    pub fn warn(msg: String, span: Option<SourceSpan>) -> Self {
        Self {
            msg,
            span,
            verbose: false,
            is_warning: true,
        }
    }
}

/// Prints a formatted error report to stderr.
///
/// # Arguments
///
/// * `report` - The report to print.
pub fn report(report: &Report, fm: &FileManager) {
    let config = Config::default().with_color(colors_enabled());
    let msg = &report.msg;
    let kind = if report.is_warning {
        ReportKind::Warning
    } else {
        ReportKind::Error
    };

    let code = 3;

    let (path, diag_span) = match report.span {
        Some(span) => {
            let path = fm.get_path(span.file_id()).unwrap();
            let diag_span = DiagnosticSpan(path.to_string_lossy().to_string(), span);
            (path.to_path_buf(), diag_span)
        }
        None => {
            let path = PathBuf::from("<input>");
            let span = SourceSpan::default();
            let diag_span = DiagnosticSpan(path.to_string_lossy().to_string(), span);
            (path, diag_span)
        }
    };

    let start_offset = diag_span.1.start_offset() as usize;
    let ariadne = AriadneReport::build(kind, path.to_string_lossy().to_string(), start_offset);
    let ariadne = ariadne
        .with_code(code)
        .with_message(msg)
        .with_config(config);

    // label
    let file_id = diag_span.1.file_id();
    let file_name = diag_span.0.to_string();
    let ariadne = ariadne
        .with_label(
            Label::new(diag_span)
                .with_message(msg.fg(Color::Red))
                .with_color(Color::Red),
        )
        .finish();

    let source = Source::from(fm.read(file_id).unwrap());
    ariadne.eprint((file_name, source)).unwrap();
}
