use crate::ast::StringId;
use crate::diagnostic::{DiagDisplay, DiagFormatter, Diagnostic, DiagnosticLevel, format_diag_without_registry};
use crate::source_manager::SourceSpan;
use std::fmt::Write;

/// Preprocessor errors
#[derive(Debug)]
pub enum PPError {
    FileNotFound { path: String },
    IncludeDepthExceeded,
    ExpectedIdentifier,
    InvalidDirective,
    UnexpectedEndOfFile,
    InvalidMacroParameter,
    InvalidIncludePath,
    UnmatchedEndif,
    ErrorDirective(String),
    InvalidConditionalExpression,
    DivisionByZero,
    RemainderByZero,
    InvalidLineDirective,
    MultipleElse,
    ElifAfterElse,
    ElifWithoutIf,
    ElseWithoutIf,

    ExpectedEod,
    UnknownPragma(StringId),
    InvalidPragmaPackValue(StringId),
    PragmaError(String),
    UnclosedConditional,
    InvalidUniversalCharacterName,
    MacroRedefined(StringId),
    DollarInIdentifier,
    DirectiveInMacroArgs,
    PoisonedIdentifier(StringId),
    DuplicateMacroParameter(StringId),
    ExpectedCommaInMacroParameterList,
}

impl PPError {
    pub(crate) fn is_pedantic(&self) -> bool {
        matches!(self, PPError::DollarInIdentifier | PPError::DirectiveInMacroArgs)
    }
}

impl DiagDisplay for PPError {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result {
        match self {
            PPError::FileNotFound { path } => write!(f, "File not found: {}", path),
            PPError::IncludeDepthExceeded => write!(f, "Include depth exceeded"),
            PPError::ExpectedIdentifier => write!(f, "Expected identifier"),
            PPError::InvalidDirective => write!(f, "Invalid directive"),
            PPError::UnexpectedEndOfFile => write!(f, "Unexpected end of file"),
            PPError::InvalidMacroParameter => write!(f, "Invalid macro parameter"),
            PPError::InvalidIncludePath => write!(f, "Invalid include path"),
            PPError::UnmatchedEndif => write!(f, "Unmatched #endif"),
            PPError::ErrorDirective(msg) => write!(f, "#error directive: {}", msg),
            PPError::InvalidConditionalExpression => write!(f, "Invalid conditional expression"),
            PPError::DivisionByZero => write!(f, "division by zero in preprocessor expression"),
            PPError::RemainderByZero => write!(f, "remainder by zero in preprocessor expression"),
            PPError::InvalidLineDirective => write!(f, "Invalid #line directive"),
            PPError::MultipleElse => write!(f, "Multiple #else directives"),
            PPError::ElifAfterElse => write!(f, "#elif after #else"),
            PPError::ElifWithoutIf => write!(f, "#elif without #if"),
            PPError::ElseWithoutIf => write!(f, "#else without #if"),

            PPError::ExpectedEod => write!(f, "Expected end of directive"),
            PPError::UnknownPragma(pragma) => write!(f, "Unknown pragma: {}", pragma),
            PPError::InvalidPragmaPackValue(val) => write!(f, "Invalid Pragma Pack Value: {}", val),
            PPError::PragmaError(msg) => write!(f, "Pragma error: {}", msg),
            PPError::UnclosedConditional => write!(f, "Unclosed preprocessor conditional directive"),
            PPError::InvalidUniversalCharacterName => write!(f, "Invalid universal character name"),
            PPError::MacroRedefined(macro_name) => {
                write!(f, "Macro '{}' redefined with different value", macro_name)
            }
            PPError::DollarInIdentifier => write!(f, "'$' in identifier or number"),
            PPError::DirectiveInMacroArgs => {
                write!(f, "embedding a directive within macro arguments is not portable")
            }
            PPError::PoisonedIdentifier(name) => {
                write!(f, "attempt to use poisoned identifier '{}'", name)
            }
            PPError::DuplicateMacroParameter(param) => {
                write!(f, "duplicate macro parameter name '{}'", param)
            }
            PPError::ExpectedCommaInMacroParameterList => {
                write!(f, "expected comma in macro parameter list")
            }
        }
    }
}

impl std::fmt::Display for PPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = format_diag_without_registry(self);
        f.write_str(&msg)
    }
}

impl std::error::Error for PPError {}

#[derive(Debug)]
pub struct PPDiag {
    pub kind: PPError,
    pub span: SourceSpan,
}

impl DiagDisplay for PPDiag {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::fmt::Display for PPDiag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = format_diag_without_registry(&self.kind);
        f.write_str(&msg)
    }
}

impl std::error::Error for PPDiag {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.kind)
    }
}

impl From<PPDiag> for Diagnostic {
    fn from(val: PPDiag) -> Self {
        let level = DiagnosticLevel::Error;

        Diagnostic {
            level,
            message: format_diag_without_registry(&val.kind),
            span: val.span,
            ..Default::default()
        }
    }
}

impl crate::diagnostic::IntoDiagnostic for PPDiag {
    fn into_diagnostic(self) -> Vec<Diagnostic> {
        let span = self.span;
        let kind = self.kind;
        let warning_name = match &kind {
            PPError::DollarInIdentifier => Some("dollar-in-identifier-extension"),
            PPError::MacroRedefined(_) => Some("macro-redefined"),
            PPError::DirectiveInMacroArgs => Some("embedded-directive"),
            PPError::UnknownPragma(_) => Some("unknown-pragmas"),
            _ => None,
        };
        let mut diag = Diagnostic {
            level: DiagnosticLevel::Error,
            message: format_diag_without_registry(&kind),
            span,
            warning_name,
            ..Default::default()
        };

        // Add hints for certain error types
        match &kind {
            PPError::ElifWithoutIf => {
                diag.hints.push("perhaps you meant to use #if?".to_string());
            }
            PPError::ElseWithoutIf => {
                diag.hints
                    .push("perhaps you meant to use #ifdef or #ifndef?".to_string());
            }
            PPError::UnmatchedEndif => {
                diag.hints
                    .push("this #endif does not have a matching #if, #ifdef, or #ifndef".to_string());
            }
            PPError::MultipleElse => {
                diag.hints
                    .push("there can only be one #else directive per conditional level".to_string());
            }
            PPError::ElifAfterElse => {
                diag.hints
                    .push("#elif directives must come before the #else directive".to_string());
            }
            _ => {}
        }

        vec![diag]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::IntoDiagnostic;

    #[test]
    fn test_error_hints() {
        let cases = vec![
            (PPError::ElifWithoutIf, "perhaps you meant to use #if?"),
            (PPError::ElseWithoutIf, "perhaps you meant to use #ifdef or #ifndef?"),
            (
                PPError::UnmatchedEndif,
                "this #endif does not have a matching #if, #ifdef, or #ifndef",
            ),
            (
                PPError::MultipleElse,
                "there can only be one #else directive per conditional level",
            ),
            (
                PPError::ElifAfterElse,
                "#elif directives must come before the #else directive",
            ),
            (PPError::IncludeDepthExceeded, ""),
        ];

        for (kind, hint) in cases {
            let err = PPDiag {
                kind,
                span: SourceSpan::default(),
            };
            let diags = err.into_diagnostic();
            assert_eq!(diags.len(), 1);
            if hint.is_empty() {
                assert!(diags[0].hints.is_empty());
            } else {
                assert_eq!(diags[0].hints[0], hint);
            }
        }
    }

    #[test]
    fn test_error_formatting_and_diagnostic() {
        use std::error::Error;
        let err = PPDiag {
            kind: PPError::IncludeDepthExceeded,
            span: SourceSpan::default(),
        };
        assert_eq!(err.to_string(), "Include depth exceeded");
        assert!(err.source().is_some());

        let diag: Diagnostic = err.into();
        assert_eq!(diag.message, "Include depth exceeded");
        assert_eq!(diag.level, DiagnosticLevel::Error);

        let err_macro = PPDiag {
            kind: PPError::MacroRedefined(StringId::new("TEST")),
            span: SourceSpan::default(),
        };
        assert_eq!(err_macro.to_string(), "Macro 'TEST' redefined with different value");
    }
}
