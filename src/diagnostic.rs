use crate::semantic::{QualType, TypeRef, TypeRegistry};
use crate::source_manager::{FileKind, SourceManager, SourceSpan};
use hashbrown::HashSet;
use std::io::IsTerminal;

use annotate_snippets::renderer::DecorStyle;
use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};

/// Diagnostic severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum DiagnosticLevel {
    #[default]
    Error,
    Warning,
    Note,
}

/// Individual diagnostic with rich context
#[derive(Debug, Clone, Default)]
pub(crate) struct Diagnostic {
    pub(crate) level: DiagnosticLevel,
    pub(crate) message: String,
    pub(crate) span: SourceSpan,
    pub(crate) hints: Vec<String>, // Suggestions for fixing
    pub(crate) warning_name: Option<&'static str>,
    pub(crate) is_streamed: bool,
}

/// Diagnostic engine for collecting and reporting semantic errors and warnings
pub(crate) struct DiagnosticEngine {
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// Bolt ⚡: Cached error count for O(1) checks and improved performance
    /// when error limits are applied.
    pub(crate) error_count: usize,
    pub(crate) error_limit: Option<usize>,
    pub(crate) warning_count: usize,
    pub(crate) warning_limit: Option<usize>,
    /// Bolt ⚡: Flag to ensure the "too many errors" note is only emitted once.
    pub(crate) error_limit_reached: bool,
    /// Bolt ⚡: Flag to ensure the "too many warnings" note is only emitted once.
    pub(crate) warning_limit_reached: bool,
    pub(crate) disabled_warnings: HashSet<String>,
    pub(crate) diagnostic_stack: Vec<HashSet<String>>,
    pub(crate) renderer: Renderer,
}

impl Default for DiagnosticEngine {
    fn default() -> Self {
        let use_colors = std::io::stderr().is_terminal();
        let renderer = if use_colors {
            Renderer::styled().decor_style(DecorStyle::Unicode)
        } else {
            Renderer::plain()
        };

        Self {
            diagnostics: Vec::new(),
            error_count: 0,
            error_limit: None,
            warning_count: 0,
            warning_limit: None,
            error_limit_reached: false,
            warning_limit_reached: false,
            disabled_warnings: HashSet::new(),
            diagnostic_stack: Vec::new(),
            renderer,
        }
    }
}

impl DiagnosticEngine {
    pub(crate) fn from_warnings(warnings: &[String]) -> Self {
        let mut disabled_warnings = HashSet::new();
        for w in warnings {
            if let Some(stripped) = w.strip_prefix("no-") {
                disabled_warnings.insert(stripped.to_string());
            }
        }

        let use_colors = std::io::stderr().is_terminal();
        let renderer = if use_colors {
            Renderer::styled().decor_style(DecorStyle::Unicode)
        } else {
            Renderer::plain()
        };

        Self {
            diagnostics: Vec::new(),
            error_count: 0,
            error_limit: None,
            warning_count: 0,
            warning_limit: None,
            error_limit_reached: false,
            warning_limit_reached: false,
            disabled_warnings,
            diagnostic_stack: Vec::new(),
            renderer,
        }
    }

    pub(crate) fn push_diagnostics(&mut self) {
        self.diagnostic_stack.push(self.disabled_warnings.clone());
    }

    pub(crate) fn pop_diagnostics(&mut self) {
        if let Some(state) = self.diagnostic_stack.pop() {
            self.disabled_warnings = state;
        }
    }

    pub(crate) fn set_error_limit(&mut self, limit: usize) {
        self.error_limit = Some(limit);
    }

    pub(crate) fn set_warning_limit(&mut self, limit: usize) {
        self.warning_limit = Some(limit);
    }

    pub(crate) fn report_diagnostic(&mut self, diagnostic: Diagnostic) {
        if diagnostic.level == DiagnosticLevel::Warning
            && diagnostic
                .warning_name
                .is_some_and(|name| self.disabled_warnings.contains(name))
        {
            return;
        }

        if diagnostic.level == DiagnosticLevel::Error {
            if let Some(limit) = self.error_limit
                && self.error_count >= limit
            {
                if self.error_limit_reached == false {
                    // Report that we reached the limit
                    // Use the span of the current error to avoid <unknown> source if possible
                    self.diagnostics.push(Diagnostic {
                        level: DiagnosticLevel::Note,
                        message: format!("too many errors emitted, stopping after {} errors", limit),
                        span: diagnostic.span,
                        ..Default::default()
                    });
                    self.error_limit_reached = true;
                }
                return;
            }
            self.error_count += 1;
        } else if diagnostic.level == DiagnosticLevel::Warning {
            if let Some(limit) = self.warning_limit
                && self.warning_count >= limit
            {
                if !self.warning_limit_reached {
                    self.diagnostics.push(Diagnostic {
                        level: DiagnosticLevel::Note,
                        message: format!("too many warnings emitted, stopping after {} warnings", limit),
                        span: diagnostic.span,
                        ..Default::default()
                    });
                    self.warning_limit_reached = true;
                }
                return;
            }
            self.warning_count += 1;
        }

        self.diagnostics.push(diagnostic);
    }

    pub(crate) fn has_errors(&self) -> bool {
        self.error_count > 0
    }

    pub(crate) fn report_streaming(&mut self, mut diagnostic: Diagnostic, source_manager: &SourceManager) {
        let prev_len = self.diagnostics.len();
        diagnostic.is_streamed = true;
        self.report_diagnostic(diagnostic);
        if self.diagnostics.len() > prev_len {
            let added_diag = self.diagnostics.last().unwrap();
            let formatted = self.format_diagnostic(added_diag, source_manager);
            eprintln!("{}", formatted);
        }
    }

    pub(crate) fn report_semantic_streaming(
        &mut self,
        err: crate::semantic::errors::SemanticDiag,
        source_manager: &SourceManager,
        registry: &crate::semantic::TypeRegistry,
    ) {
        for diag in err.into_diagnostic(registry) {
            self.report_streaming(diag, source_manager);
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
        let (start, end, start_line) = source_manager.get_line_window(span.source_id(), span.start().offset(), 3);
        let source_full = source_manager.get_source_str(span.source_id());
        let source_slice = &source_full[start as usize..end as usize];

        let path = source_manager
            .get_file_info(span.source_id())
            .map(|fi| fi.path.to_str().unwrap_or("<unknown>"))
            .unwrap_or("<unknown>");

        let mut snippet = Snippet::source(source_slice).line_start(start_line as usize).path(path);

        let annotation_kind = AnnotationKind::Primary;

        let rel_start = span.start().offset().saturating_sub(start) as usize;
        let rel_end = (span.end().offset().saturating_sub(start) as usize).min(source_slice.len());

        snippet = snippet.annotation(annotation_kind.span(rel_start..rel_end).label(message));

        snippet
    }

    /// Format a single diagnostic with rich source code context
    pub(crate) fn format_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let message = if diag.level == DiagnosticLevel::Warning {
            if let Some(name) = diag.warning_name {
                format!("{} [-W{}]", diag.message, name)
            } else {
                diag.message.clone()
            }
        } else {
            diag.message.clone()
        };

        // If it's a built-in source ID (e.g. command line define), simple print
        if diag.span.is_source_id_builtin() {
            return format!("{}: {}", self.format_location(diag, source_manager), message);
        }

        // Primary error snippet
        let snippet = self.create_snippet(diag.span, "", source_manager);
        // Use primary_title instead of title
        let mut group = self.level(diag).primary_title(&message).element(snippet);

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
                let note_msg = if file_info.kind == FileKind::MacroExpansion {
                    format!("expanded from macro '{}'", file_info.path.to_string_lossy())
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
        self.renderer.render(report)
    }

    /// Print diagnostics, skipping warnings if suppress_warnings is true
    pub(crate) fn print_diagnostics_filtered(&self, source_manager: &SourceManager, suppress_warnings: bool) {
        for diag in &self.diagnostics {
            if diag.is_streamed {
                continue;
            }
            if suppress_warnings && diag.level == DiagnosticLevel::Warning {
                continue;
            }
            let formatted = self.format_diagnostic(diag, source_manager);
            eprintln!("{}", formatted);
        }
    }
}

pub(crate) trait IntoDiagnostic {
    fn into_diagnostic(self) -> Vec<Diagnostic>;
}

pub(crate) struct DiagFormatter<'a> {
    pub(crate) registry: Option<&'a TypeRegistry>,
    buffer: String,
}

impl<'a> DiagFormatter<'a> {
    pub(crate) fn new(registry: &'a TypeRegistry) -> Self {
        Self {
            registry: Some(registry),
            buffer: String::new(),
        }
    }

    pub(crate) fn new_without_registry() -> Self {
        Self {
            registry: None,
            buffer: String::new(),
        }
    }

    pub(crate) fn display_qual_type(&self, ty: QualType) -> String {
        self.registry
            .expect("TypeRegistry required to display type")
            .display_qual_type(ty)
    }

    pub(crate) fn display_type(&self, ty: TypeRef) -> String {
        self.registry
            .expect("TypeRegistry required to display type")
            .display_type(ty)
    }

    pub(crate) fn into_string(self) -> String {
        self.buffer
    }
}

impl<'a> std::fmt::Write for DiagFormatter<'a> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.buffer.write_str(s)
    }
}

pub(crate) trait DiagDisplay {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result;
}

pub(crate) fn format_diag(registry: &TypeRegistry, diag: &impl DiagDisplay) -> String {
    let mut f = DiagFormatter::new(registry);
    let _ = diag.fmt(&mut f);
    f.into_string()
}

pub(crate) fn format_diag_without_registry(diag: &impl DiagDisplay) -> String {
    let mut f = DiagFormatter::new_without_registry();
    let _ = diag.fmt(&mut f);
    f.into_string()
}
