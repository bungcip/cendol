use crate::{
    ast::NameId,
    parser::TokenKind,
    semantic::TypeRef,
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
    pub code: Option<String>,     // Error code like "E001"
    pub hints: Vec<String>,       // Suggestions for fixing
    pub related: Vec<SourceSpan>, // Related locations
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
#[derive(Default)]
pub struct DiagnosticEngine {
    pub diagnostics: Vec<Diagnostic>,
    pub warnings_as_errors: bool,
    pub disable_all_warnings: bool,
    pub error_limit: Option<usize>,
}

impl DiagnosticEngine {
    pub(crate) fn from_warnings(warnings: &[String]) -> Self {
        let warnings_as_errors = warnings.iter().any(|w| w == "error");
        let disable_all_warnings = warnings.iter().any(|w| w == "no-warnings");
        Self {
            diagnostics: Vec::new(),
            warnings_as_errors,
            disable_all_warnings,
            error_limit: None,
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

    pub(crate) fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub(crate) fn report<T: IntoDiagnostic>(&mut self, error: T) {
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
            span: self.span,
            ..Default::default()
        }]
    }
}

impl IntoDiagnostic for SemanticError {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        // Determine if this should be a warning or error
        let level = match &self.kind {
            SemanticErrorKind::EmptyDeclaration { .. } => DiagnosticLevel::Warning,
            _ => DiagnosticLevel::Error,
        };

        let mut diagnostics = vec![Diagnostic {
            level,
            message: self.to_string(),
            span: self.span,
            ..Default::default()
        }];

        match &self.kind {
            SemanticErrorKind::Redefinition { first_def, .. }
            | SemanticErrorKind::RedefinitionWithDifferentType { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous definition is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            SemanticErrorKind::GenericMultipleDefault { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous default association is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            SemanticErrorKind::GenericDuplicateMatch { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous association is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            SemanticErrorKind::ConflictingLinkage { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous declaration is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            SemanticErrorKind::DuplicateMember { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous declaration is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            SemanticErrorKind::ConflictingTypes { first_def, .. } => {
                diagnostics.push(Diagnostic {
                    level: DiagnosticLevel::Note,
                    message: "previous declaration is here".to_string(),
                    span: *first_def,
                    ..Default::default()
                });
            }
            _ => {}
        }

        // Handle warnings
        if matches!(
            self.kind,
            SemanticErrorKind::IncompatiblePointerComparison { .. }
                | SemanticErrorKind::IncompatiblePointerTypes { .. }
                | SemanticErrorKind::ReturnLocalAddress { .. }
                | SemanticErrorKind::ImplicitConstantConversion { .. }
                | SemanticErrorKind::SwitchCaseOverflow { .. }
                | SemanticErrorKind::AddressOfArrayAlwaysTrue { .. }
        ) {
            diagnostics[0].level = DiagnosticLevel::Warning;
        }

        diagnostics
    }
}
#[derive(Debug, Error)]
#[error("{kind}")]
pub struct SemanticError {
    pub span: SourceSpan,
    pub kind: SemanticErrorKind,
}

/// Semantic errors
#[derive(Debug, Error)]
pub enum SemanticErrorKind {
    #[error("variable has incomplete type 'void'")]
    VariableOfVoidType,
    #[error("called object type '{ty}' is not a function or function pointer")]
    CalledNonFunctionType { ty: String },
    #[error("Undeclared identifier '{name}'")]
    UndeclaredIdentifier { name: NameId },
    #[error("redefinition of '{name}'")]
    Redefinition { name: NameId, first_def: SourceSpan },
    #[error("redefinition of '{name}' with a different type")]
    RedefinitionWithDifferentType { name: NameId, first_def: SourceSpan },
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },
    #[error("Expression is not assignable (not an lvalue)")]
    NotAnLvalue,
    #[error("Invalid operands for binary operation: have '{left_ty}' and '{right_ty}'")]
    InvalidBinaryOperands { left_ty: String, right_ty: String },
    #[error("Invalid operand for unary operation: have '{ty}'")]
    InvalidUnaryOperand { ty: String },
    #[error("indirection requires pointer operand ('{ty}' invalid)")]
    IndirectionRequiresPointer { ty: String },
    #[error("Initializer element is not a compile-time constant")]
    NonConstantInitializer,
    #[error("invalid initializer")]
    InvalidInitializer,
    #[error("conflicting types for '{name}'")]
    ConflictingTypes { name: String, first_def: SourceSpan },
    #[error("void function '{name}' should not return a value")]
    VoidReturnWithValue { name: String },
    #[error("non-void function '{name}' should return a value")]
    NonVoidReturnWithoutValue { name: String },

    #[error("invalid number of arguments: expected {expected}, found {found}")]
    InvalidNumberOfArguments { expected: usize, found: usize },

    #[error("invalid argument type for atomic builtin: {ty}")]
    InvalidAtomicArgument { ty: String },

    #[error("excess elements in {kind} initializer")]
    ExcessElements { kind: String },

    #[error("Unsupported feature: {feature}")]
    UnsupportedFeature { feature: String },

    #[error("size of array has non-positive value")]
    InvalidArraySize,

    #[error("invalid bit-field width")]
    InvalidBitfieldWidth,

    #[error("bit-field width is not a constant expression")]
    NonConstantBitfieldWidth,

    #[error("width of bit-field ({width} bits) exceeds width of its type ({type_width} bits)")]
    BitfieldWidthExceedsType { width: u16, type_width: u64 },

    #[error("zero-width bit-field shall not specify a declarator")]
    NamedZeroWidthBitfield,

    #[error("bit-field type '{ty}' is invalid")]
    InvalidBitfieldType { ty: String },

    #[error("bit-field shall not have an atomic type")]
    BitfieldHasAtomicType,

    // Errors related to declaration specifiers
    #[error("conflicting storage class specifiers")]
    ConflictingStorageClasses,
    #[error("conflicting linkage for '{name}'")]
    ConflictingLinkage { name: String, first_def: SourceSpan },
    #[error("cannot combine with previous '{prev}' declaration specifier")]
    ConflictingTypeSpecifiers { prev: String },
    #[error("'{spec}' function specifier appears on non-function declaration")]
    InvalidFunctionSpecifier { spec: String },
    #[error("duplicate member '{name}'")]
    DuplicateMember { name: NameId, first_def: SourceSpan },
    #[error("member reference base type '{ty}' is not a structure or union")]
    MemberAccessOnNonRecord { ty: String },
    #[error("member '{name}' has function type")]
    MemberHasFunctionType { name: NameId },
    #[error("no member named '{name}' in '{ty}'")]
    MemberNotFound { name: NameId, ty: String },
    #[error("expected a typedef name, found {found}")]
    ExpectedTypedefName { found: String },
    #[error("missing type specifier in declaration")]
    MissingTypeSpecifier,
    #[error("static assertion failed: {message}")]
    StaticAssertFailed { message: String },
    #[error("expression in static assertion is not constant")]
    StaticAssertNotConstant,
    #[error("recursive type definition")]
    RecursiveType { ty: TypeRef },
    #[error("Invalid application of 'sizeof' to an incomplete type")]
    SizeOfIncompleteType { ty: TypeRef },
    #[error("Invalid application of 'sizeof' to a function type")]
    SizeOfFunctionType,
    #[error("Invalid application of '_Alignof' to an incomplete type")]
    AlignOfIncompleteType { ty: TypeRef },
    #[error("Invalid application of '_Alignof' to a function type")]
    AlignOfFunctionType,
    #[error("controlling expression type '{ty}' not compatible with any generic association")]
    GenericNoMatch { ty: String },

    #[error("generic association specifies function type '{ty}'")]
    GenericFunctionAssociation { ty: String },

    #[error("generic association specifies variably modified type '{ty}'")]
    GenericVlaAssociation { ty: String },

    #[error("cannot take address of bit-field")]
    AddressOfBitfield,

    #[error("cannot take address of 'register' variable")]
    AddressOfRegister,

    #[error("cannot apply 'sizeof' to a bit-field")]
    SizeOfBitfield,

    #[error("controlling expression type '{ty}' is an incomplete type")]
    GenericIncompleteControl { ty: String },

    #[error("generic association specifies incomplete type '{ty}'")]
    GenericIncompleteAssociation { ty: String },

    #[error("duplicate default association in generic selection")]
    GenericMultipleDefault { first_def: SourceSpan },

    #[error("type '{ty}' in generic association compatible with previously specified type '{prev_ty}'")]
    GenericDuplicateMatch {
        ty: String,
        prev_ty: String,
        first_def: SourceSpan,
    },

    #[error("requested alignment is not a positive power of 2")]
    InvalidAlignment { value: i64 },

    #[error("requested alignment is not a constant expression")]
    NonConstantAlignment,

    #[error("cannot assign to read-only location")]
    AssignmentToReadOnly,

    #[error("incomplete type '{ty}'")]
    IncompleteType { ty: String },

    #[error("function has incomplete return type")]
    IncompleteReturnType,

    #[error("comparison of incompatible pointer types '{lhs}' and '{rhs}'")]
    IncompatiblePointerComparison { lhs: String, rhs: String },

    #[error("incompatible pointer types passing '{found}' to parameter of type '{expected}'")]
    IncompatiblePointerTypes { expected: String, found: String },

    #[error("'case' or 'default' label not in switch statement")]
    CaseNotInSwitch,

    #[error("duplicate case value '{value}'")]
    DuplicateCase { value: String },

    #[error("expression in 'case' label is not an integer constant expression")]
    NonConstantCaseValue,

    #[error("switch condition has non-integer type '{ty}'")]
    InvalidSwitchCondition { ty: String },

    #[error("multiple default labels in one switch")]
    MultipleDefaultLabels,

    #[error("flexible array member must be the last member of a structure")]
    FlexibleArrayNotLast,

    #[error("flexible array member in otherwise empty structure")]
    FlexibleArrayInEmptyStruct,

    #[error("restrict requires a pointer type")]
    InvalidRestrict,
    #[error("invalid storage class for function parameter")]
    InvalidStorageClassForParameter,
    #[error("function '{name}' declared '_Noreturn' contains a return statement")]
    NoreturnFunctionHasReturn { name: String },
    #[error("function '{name}' declared '_Noreturn' can fall off the end")]
    NoreturnFunctionFallsOff { name: String },

    #[error("alignment specifier cannot be used in a {context}")]
    AlignmentNotAllowed { context: String },

    #[error("alignment specifier specifies {requested}-byte alignment, but {natural}-byte alignment is required")]
    AlignmentTooLoose { requested: u32, natural: u32 },

    #[error("_Atomic qualifier cannot be used with {type_kind} type")]
    InvalidAtomicQualifier { type_kind: String },

    #[error("_Atomic(type-name) specifier cannot be used with {reason}")]
    InvalidAtomicSpecifier { reason: String },

    #[error("static in array declarator only allowed in function parameters")]
    ArrayStaticOutsideParameter,

    #[error("type qualifiers in array declarator only allowed in function parameters")]
    ArrayQualifierOutsideParameter,

    #[error("static in array declarator only allowed in outermost array type")]
    ArrayStaticNotOutermost,

    #[error("type qualifiers in array declarator only allowed in outermost array type")]
    ArrayQualifierNotOutermost,

    #[error("break statement not in loop or switch")]
    BreakNotInLoop,

    #[error("continue statement not in loop statement")]
    ContinueNotInLoop,

    #[error("subscripted value is not an array (have '{found}')")]
    ExpectedArrayType { found: String },

    #[error("invalid designator in 'offsetof'")]
    InvalidOffsetofDesignator,

    #[error("address of stack memory associated with local variable '{name}' returned")]
    ReturnLocalAddress { name: NameId },

    #[error("implicit conversion from '{from}' to '{to}' changes value from {from_val} to {to_val}")]
    ImplicitConstantConversion {
        from: String,
        to: String,
        from_val: String,
        to_val: String,
    },

    #[error("overflow converting case value to switch condition type ({from} to {to})")]
    SwitchCaseOverflow { from: String, to: String },

    #[error("address of array '{name}' will always evaluate to 'true'")]
    AddressOfArrayAlwaysTrue { name: NameId },

    #[error("declaration does not declare anything")]
    EmptyDeclaration,
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
        let snippet = self.create_snippet(diag.span, &diag.message, source_manager);
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
    pub(crate) fn print_diagnostics(&self, diagnostics: &[Diagnostic], source_manager: &SourceManager) {
        for diag in diagnostics {
            let formatted = self.format_diagnostic(diag, source_manager);
            eprintln!("{}", formatted);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_manager::SourceSpan;

    #[test]
    fn test_error_spans() {
        let span = SourceSpan::dummy();

        let p1 = ParseError {
            span,
            kind: ParseErrorKind::UnexpectedEof,
        };
        assert_eq!(p1.span, span);

        let p3 = ParseError {
            span,
            kind: ParseErrorKind::DeclarationNotAllowed,
        };
        assert_eq!(p3.span, span);

        let s1 = SemanticError {
            span,
            kind: SemanticErrorKind::NonConstantInitializer,
        };
        assert_eq!(s1.span, span);

        let s2 = SemanticError {
            span,
            kind: SemanticErrorKind::InvalidInitializer,
        };
        assert_eq!(s2.span, span);
    }
}
