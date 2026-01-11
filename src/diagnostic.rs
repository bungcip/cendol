use crate::ast::NameId;
use crate::lexer::TokenKind;
use crate::semantic::TypeRef;
use crate::source_manager::{SourceManager, SourceSpan};
use annotate_snippets::renderer::DecorStyle;
use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};

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
    pub code: Option<String>,     // Error code like "E001"
    pub hints: Vec<String>,       // Suggestions for fixing
    pub related: Vec<SourceSpan>, // Related locations
}

/// Parse errors
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("Unexpected token: expected {expected_tokens}, found {found:?}")]
    UnexpectedToken {
        expected_tokens: String,
        found: TokenKind,
        span: SourceSpan,
    },

    #[error("Unexpected End of File")]
    UnexpectedEof { span: SourceSpan },

    #[error("Invalid unary operator")]
    InvalidUnaryOperator { span: SourceSpan },

    #[error("Declaration not allowed in this context")]
    DeclarationNotAllowed { span: SourceSpan },

    #[error("Parser exceeded maximum iteration limit - possible infinite loop")]
    InfiniteLoop { span: SourceSpan },
}

impl ParseError {
    pub fn span(&self) -> SourceSpan {
        match self {
            ParseError::UnexpectedToken { span, .. } => *span,
            ParseError::UnexpectedEof { span } => *span,
            ParseError::InvalidUnaryOperator { span } => *span,
            ParseError::DeclarationNotAllowed { span } => *span,
            ParseError::InfiniteLoop { span } => *span,
        }
    }
}
/// Diagnostic engine for collecting and reporting semantic errors and warnings
pub struct DiagnosticEngine {
    pub diagnostics: Vec<Diagnostic>,
    pub warnings_as_errors: bool,
    pub disable_all_warnings: bool,
}

impl Default for DiagnosticEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl DiagnosticEngine {
    pub fn new() -> Self {
        DiagnosticEngine {
            diagnostics: Vec::new(),
            warnings_as_errors: false,
            disable_all_warnings: false,
        }
    }

    pub fn from_warnings(warnings: &[String]) -> Self {
        let warnings_as_errors = warnings.iter().any(|w| w == "error");
        let disable_all_warnings = warnings.iter().any(|w| w == "no-warnings");
        Self {
            diagnostics: Vec::new(),
            warnings_as_errors,
            disable_all_warnings,
        }
    }

    fn _report(&mut self, level: DiagnosticLevel, message: String, span: SourceSpan) {
        if level == DiagnosticLevel::Warning && self.disable_all_warnings {
            return;
        }

        let final_level = if level == DiagnosticLevel::Warning && self.warnings_as_errors {
            DiagnosticLevel::Error
        } else {
            level
        };

        self.diagnostics.push(Diagnostic {
            level: final_level,
            message,
            span,
            ..Default::default()
        });
    }

    // pub(crate) fn report_note(&mut self, message: String, span: SourceSpan) {
    //     self._report(DiagnosticLevel::Note, message, span);
    // }

    pub fn report_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.level == DiagnosticLevel::Error)
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn report<T: IntoDiagnostic>(&mut self, error: T) {
        for diagnostic in error.into_diagnostic() {
            self.report_diagnostic(diagnostic);
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
            span: self.span(),
            ..Default::default()
        }]
    }
}

impl IntoDiagnostic for SemanticError {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        let mut diagnostics = vec![Diagnostic {
            level: DiagnosticLevel::Error,
            message: self.to_string(),
            span: self.span(),
            ..Default::default()
        }];

        if let SemanticError::Redefinition { first_def, .. } = &self {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Note,
                message: "previous definition is here".to_string(),
                span: *first_def,
                ..Default::default()
            });
        }

        // Handle warnings
        if matches!(self, SemanticError::IncompatiblePointerComparison { .. }) {
            diagnostics[0].level = DiagnosticLevel::Warning;
        }

        diagnostics
    }
}
/// Semantic errors
#[derive(Debug, thiserror::Error)]
pub enum SemanticError {
    #[error("Undeclared identifier '{name}'")]
    UndeclaredIdentifier { name: NameId, span: SourceSpan },
    #[error("redefinition of '{name}'")]
    Redefinition {
        name: NameId,
        first_def: SourceSpan,
        span: SourceSpan,
    },
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        span: SourceSpan,
    },
    #[error("Expression is not assignable (not an lvalue)")]
    NotAnLvalue { span: SourceSpan },
    #[error("Invalid operands for binary operation: have '{left_ty}' and '{right_ty}'")]
    InvalidBinaryOperands {
        left_ty: String,
        right_ty: String,
        span: SourceSpan,
    },
    #[error("Invalid operand for unary operation: have '{ty}'")]
    InvalidUnaryOperand { ty: String, span: SourceSpan },
    #[error("Initializer element is not a compile-time constant")]
    NonConstantInitializer { span: SourceSpan },
    #[error("Invalid use of void type in expression")]
    InvalidUseOfVoid { span: SourceSpan },
    #[error("Unsupported feature: {feature}")]
    UnsupportedFeature { feature: String, span: SourceSpan },

    #[error("size of array has non-positive value")]
    InvalidArraySize { span: SourceSpan },

    #[error("bit-field has non-positive width")]
    InvalidBitfieldWidth { span: SourceSpan },

    #[error("bit-field width is not a constant expression")]
    NonConstantBitfieldWidth { span: SourceSpan },

    // Errors related to declaration specifiers
    #[error("conflicting storage class specifiers")]
    ConflictingStorageClasses { span: SourceSpan },
    #[error("member reference base type '{ty}' is not a structure or union")]
    MemberAccessOnNonRecord { ty: String, span: SourceSpan },
    #[error("no member named '{name}' in '{ty}'")]
    MemberNotFound { name: NameId, ty: String, span: SourceSpan },
    #[error("expected a typedef name, found {found}")]
    ExpectedTypedefName { found: String, span: SourceSpan },
    #[error("missing type specifier in declaration")]
    MissingTypeSpecifier { span: SourceSpan },
    #[error("static assertion failed: {message}")]
    StaticAssertFailed { message: String, span: SourceSpan },
    #[error("expression in static assertion is not constant")]
    StaticAssertNotConstant { span: SourceSpan },
    #[error("recursive type definition")]
    RecursiveType { ty: TypeRef },
    #[error("Invalid application of 'sizeof' to an incomplete type")]
    SizeOfIncompleteType { ty: TypeRef, span: SourceSpan },
    #[error("controlling expression type does not match any generic association")]
    GenericNoMatch { span: SourceSpan },

    #[error("requested alignment {value} is not a power of 2")]
    InvalidAlignment { value: i64, span: SourceSpan },

    #[error("requested alignment is not a constant expression")]
    NonConstantAlignment { span: SourceSpan },

    #[error("cannot assign to read-only location")]
    AssignmentToReadOnly { span: SourceSpan },

    #[error("incomplete type '{ty}'")]
    IncompleteType { ty: String, span: SourceSpan },

    #[error("comparison of incompatible pointer types '{lhs}' and '{rhs}'")]
    IncompatiblePointerComparison { lhs: String, rhs: String, span: SourceSpan },
}

impl SemanticError {
    pub fn span(&self) -> SourceSpan {
        match self {
            SemanticError::UndeclaredIdentifier { span, .. } => *span,
            SemanticError::Redefinition { span, .. } => *span,
            SemanticError::TypeMismatch { span, .. } => *span,
            SemanticError::NotAnLvalue { span } => *span,
            SemanticError::InvalidBinaryOperands { span, .. } => *span,
            SemanticError::InvalidUnaryOperand { span, .. } => *span,
            SemanticError::NonConstantInitializer { span } => *span,
            SemanticError::InvalidUseOfVoid { span } => *span,
            SemanticError::UnsupportedFeature { span, .. } => *span,
            SemanticError::InvalidArraySize { span } => *span,
            SemanticError::InvalidBitfieldWidth { span } => *span,
            SemanticError::NonConstantBitfieldWidth { span } => *span,
            SemanticError::ConflictingStorageClasses { span } => *span,
            SemanticError::MemberAccessOnNonRecord { span, .. } => *span,
            SemanticError::MemberNotFound { span, .. } => *span,
            SemanticError::ExpectedTypedefName { span, .. } => *span,
            SemanticError::MissingTypeSpecifier { span } => *span,
            SemanticError::StaticAssertFailed { span, .. } => *span,
            SemanticError::StaticAssertNotConstant { span } => *span,
            SemanticError::RecursiveType { .. } => {
                // For recursive types, we don't have a specific span, so use a dummy span
                SourceSpan::dummy()
            }
            SemanticError::SizeOfIncompleteType { span, .. } => *span,
            SemanticError::GenericNoMatch { span } => *span,
            SemanticError::InvalidAlignment { span, .. } => *span,
            SemanticError::NonConstantAlignment { span } => *span,
            SemanticError::AssignmentToReadOnly { span } => *span,
            SemanticError::IncompleteType { span, .. } => *span,
            SemanticError::IncompatiblePointerComparison { span, .. } => *span,
        }
    }
}

/// Configurable error formatter using annotate_snippets
pub struct ErrorFormatter {
    pub show_source: bool,
    pub show_hints: bool,
    pub use_colors: bool,
    pub max_context: usize,
}

impl Default for ErrorFormatter {
    fn default() -> Self {
        ErrorFormatter {
            show_source: true,
            show_hints: true,
            use_colors: true,
            max_context: 3,
        }
    }
}

impl ErrorFormatter {
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
    pub fn format_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let renderer = if self.use_colors {
            Renderer::styled().decor_style(DecorStyle::Unicode)
        } else {
            Renderer::plain()
        };

        let message_header = match diag.level {
            DiagnosticLevel::Error => format!("error: {}", diag.message),
            DiagnosticLevel::Warning => format!("warning: {}", diag.message),
            DiagnosticLevel::Note => format!("note: {}", diag.message),
        };

        // If it's a built-in source ID (e.g. command line define), simple print
        if diag.span.is_source_id_builtin() {
            return format!("{}: {}", self.format_location(diag, source_manager), diag.message);
        }

        // Primary error snippet
        let snippet = self.create_snippet(diag.span, &diag.message, source_manager);
        // Use primary_title instead of title
        let mut group = self.level(diag).primary_title(&message_header).element(snippet);

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
    pub fn print_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) {
        for diag in diagnostics {
            let formatted = self.format_diagnostic(diag, source_manager);
            eprintln!("{}", formatted);
        }
    }
}
