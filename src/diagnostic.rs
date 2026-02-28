use crate::{
    parser::TokenKind,
    source_manager::{SourceManager, SourceSpan},
};
use annotate_snippets::renderer::DecorStyle;
use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};
use thiserror::Error;

/// Diagnostic severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DiagnosticLevel {
    #[default]
    Error,
    Warning,
    Note,
}

/// Individual diagnostic with rich context
#[derive(Debug, Clone, Default)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub span: SourceSpan,
    pub hints: Vec<String>, // Suggestions for fixing
}

/// Parse errors
#[derive(Debug, Error)]
#[error("{kind}")]
pub struct ParseError {
    pub span: SourceSpan,
    pub kind: ParseErrorKind,
}

/// Parse error kinds
#[derive(Debug, Error)]
pub enum ParseErrorKind {
    #[error("Unexpected token: expected {expected_tokens}, found {found:?}")]
    UnexpectedToken { expected_tokens: String, found: TokenKind },

    #[error("Unexpected End of File")]
    UnexpectedEof,

    #[error("Declaration not allowed in this context")]
    DeclarationNotAllowed,

    #[error("{message}")]
    Custom { message: String },
}

/// Diagnostic engine for collecting and reporting semantic errors and warnings
pub struct DiagnosticEngine {
    pub diagnostics: Vec<Diagnostic>,
    pub error_limit: Option<usize>,
    pub use_colors: bool,
}

impl Default for DiagnosticEngine {
    fn default() -> Self {
        Self {
            diagnostics: Vec::new(),
            error_limit: None,
            use_colors: true,
        }
    }
}

impl DiagnosticEngine {
    pub(crate) fn from_warnings(_warnings: &[String]) -> Self {
        Self {
            diagnostics: Vec::new(),
            error_limit: None,
            use_colors: true,
        }
    }

    pub(crate) fn set_error_limit(&mut self, limit: usize) {
        self.error_limit = Some(limit);
    }

    pub(crate) fn report_diagnostic(&mut self, diagnostic: Diagnostic) {
        if let Some(limit) = self.error_limit {
            let error_count = self
                .diagnostics
                .iter()
                .filter(|d| d.level == DiagnosticLevel::Error)
                .count();
            if error_count >= limit {
                if error_count == limit {
                    // Report that we reached the limit
                    // Use the span of the current error to avoid <unknown> source if possible
                    self.diagnostics.push(Diagnostic {
                        level: DiagnosticLevel::Note,
                        message: format!("too many errors emitted, stopping after {} errors", limit),
                        span: diagnostic.span,
                        ..Default::default()
                    });
                }
                return;
            }
        }
        self.diagnostics.push(diagnostic);
    }

    pub(crate) fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.level == DiagnosticLevel::Error)
    }

    pub(crate) fn report<T: IntoDiagnostic>(&mut self, error: T) {
        for diagnostic in error.into_diagnostic() {
            self.report_diagnostic(diagnostic);
        }
    }

    fn format_location(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let path = source_manager
            .get_file_info(diag.span.source_id())
            .map(|fi| fi.path.to_str().unwrap_or("<unknown>"))
            .unwrap_or("<unknown>");

        // Get line and column information
        let line_col = source_manager.get_line_column(diag.span.start());
        if let Some((line, col)) = line_col {
            format!("{}:{}:{}", path, line, col)
        } else {
            path.to_string()
        }
    }

    fn level<'a>(&self, diag: &Diagnostic) -> Level<'a> {
        match diag.level {
            DiagnosticLevel::Error => Level::ERROR,
            DiagnosticLevel::Warning => Level::WARNING,
            DiagnosticLevel::Note => Level::NOTE,
        }
    }

    fn create_snippet<'a>(
        &self,
        span: SourceSpan,
        message: &'a str,
        source_manager: &'a SourceManager,
    ) -> Snippet<'a, annotate_snippets::Annotation<'a>> {
        let source_buffer = source_manager.get_buffer(span.source_id());
        let source = std::str::from_utf8(source_buffer).unwrap_or("");
        let path = source_manager
            .get_file_info(span.source_id())
            .map(|fi| fi.path.to_str().unwrap_or("<unknown>"))
            .unwrap_or("<unknown>");

        let mut snippet = Snippet::source(source).line_start(1).path(path);

        let annotation_kind = AnnotationKind::Primary;

        snippet = snippet.annotation(
            annotation_kind
                .span(span.start().offset() as usize..span.end().offset() as usize)
                .label(message),
        );

        snippet
    }

    /// Format a single diagnostic with rich source code context
    fn format_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let renderer = if self.use_colors {
            Renderer::styled().decor_style(DecorStyle::Unicode)
        } else {
            Renderer::plain()
        };

        // If it's a built-in source ID (e.g. command line define), simple print
        if diag.span.is_source_id_builtin() {
            return format!("{}: {}", self.format_location(diag, source_manager), diag.message);
        }

        // Primary error snippet
        let snippet = self.create_snippet(diag.span, "", source_manager);
        // Use primary_title instead of title
        let mut group = self.level(diag).primary_title(&diag.message).element(snippet);

        for hint in &diag.hints {
            group = group.element(Level::HELP.message(hint));
        }

        // Handle macro expansion history
        // We must collect strings first to ensure they live long enough for the snippets
        let mut expansion_history = Vec::new();
        let mut current_id = diag.span.source_id();

        while let Some(file_info) = source_manager.get_file_info(current_id) {
            if let Some(include_loc) = file_info.include_loc {
                // Determine if this is a macro expansion (virtual file) or an include
                let is_macro = file_info.path.to_str().is_some_and(|s| s.starts_with("<macro_"));
                let note_msg = if is_macro {
                    let macro_name = file_info
                        .path
                        .to_str()
                        .unwrap()
                        .trim_start_matches("<macro_")
                        .trim_end_matches('>');
                    format!("expanded from macro '{}'", macro_name)
                } else {
                    "included from here".to_string()
                };

                // For visualization, use a 1-char span at the include/expansion location
                let exp_span = SourceSpan::new_with_length(include_loc.source_id(), include_loc.offset(), 1);
                expansion_history.push((exp_span, note_msg));

                current_id = include_loc.source_id();
            } else {
                break;
            }
        }

        for (span, msg) in &expansion_history {
            let exp_snippet = self.create_snippet(*span, msg, source_manager);
            group = group.element(exp_snippet);
        }

        let report = &[group];
        renderer.render(report).to_string()
    }

    /// Print all diagnostics to stderr
    pub(crate) fn print_diagnostics(&self, source_manager: &SourceManager) {
        for diag in &self.diagnostics {
            let formatted = self.format_diagnostic(diag, source_manager);
            eprintln!("{}", formatted);
        }
    }
}

pub trait IntoDiagnostic {
    fn into_diagnostic(self) -> Vec<Diagnostic>;
}

impl IntoDiagnostic for ParseError {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        vec![Diagnostic {
            level: DiagnosticLevel::Error,
            message: self.to_string(),
            span: self.span,
            ..Default::default()
        }]
    }
}
