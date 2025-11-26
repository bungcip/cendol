# Error Handling Strategy Design Document

## Overview

The Cendol compiler implements a comprehensive error handling strategy that ensures robust compilation even in the presence of errors. Errors are collected throughout the pipeline and reported with precise source locations, enabling good developer experience and IDE integration.

## Error Classification

### Error Severity Levels
- **Errors**: Fatal issues that prevent successful compilation
- **Warnings**: Potential issues that should be addressed but don't block compilation
- **Notes**: Additional information to help understand errors/warnings

### Error Categories by Phase

#### Preprocessor Errors
```rust
#[derive(Debug, thiserror::Error)]
pub enum PreprocessorError {
    #[error("Macro '{name}' redefined")]
    MacroRedefinition {
        name: Symbol,
        first_def: SourceSpan,
        second_def: SourceSpan
    },
    #[error("Undefined macro '{name}'")]
    UndefinedMacro { name: Symbol, location: SourceSpan },
    #[error("Include file not found: {path}")]
    IncludeFileNotFound { path: String, location: SourceSpan },
    #[error("Recursive include detected")]
    RecursiveInclude { file: SourceId, location: SourceSpan },
    #[error("Invalid pragma directive: {directive}")]
    InvalidPragma { directive: String, location: SourceSpan },
}
```

#### Lexer Errors
```rust
#[derive(Debug, thiserror::Error)]
pub enum LexerError {
    #[error("Invalid character '{ch}' in source")]
    InvalidCharacter { ch: char, location: SourceSpan },
    #[error("Unterminated string literal")]
    UnterminatedString { location: SourceSpan },
    #[error("Unterminated comment")]
    UnterminatedComment { location: SourceSpan },
    #[error("Invalid number literal: {text}")]
    InvalidNumber { text: String, location: SourceSpan },
}
```

#### Parser Errors
```rust
#[derive(Debug, thiserror::Error)]
pub enum ParserError {
    #[error("Unexpected token")]
    UnexpectedToken {
        expected: Vec<TokenKind>,
        found: Token,
        location: SourceSpan
    },
    #[error("Missing token: expected {expected}")]
    MissingToken { expected: TokenKind, location: SourceSpan },
    #[error("Syntax error: {message}")]
    SyntaxError { message: String, location: SourceSpan },
}
```

#### Semantic Errors
```rust
#[derive(Debug, thiserror::Error)]
pub enum SemanticError {
    #[error("Undeclared identifier '{name}'")]
    UndeclaredIdentifier { name: Symbol, location: SourceSpan },
    #[error("Redefinition of '{name}'")]
    Redefinition {
        name: Symbol,
        first_def: SourceSpan,
        second_def: SourceSpan
    },
    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        location: SourceSpan
    },
    #[error("Incomplete type '{name}'")]
    IncompleteType { name: Symbol, location: SourceSpan },
}
```

#### Warnings
```rust
#[derive(Debug, thiserror::Error)]
pub enum SemanticWarning {
    #[error("Unused declaration '{name}'")]
    UnusedDeclaration { name: Symbol, location: SourceSpan },
    #[error("Implicit conversion from {from_type} to {to_type}")]
    ImplicitConversion {
        from_type: String,
        to_type: String,
        location: SourceSpan
    },
    #[error("Unreachable code")]
    UnreachableCode { location: SourceSpan },
}
```

## Error Recovery Strategies

### Preprocessor Recovery
- **Include Errors**: Skip failed includes, continue with next tokens
- **Macro Errors**: Treat undefined macros as empty, report warnings
- **Pragma Errors**: Skip invalid pragmas, continue processing

### Lexer Recovery
- **Invalid Characters**: Skip and report, continue tokenization
- **Unterminated Literals**: Close at end of line, report error
- **Encoding Issues**: Replace invalid UTF-8 with replacement character

### Parser Recovery
- **Unexpected Tokens**: Skip to synchronization points (semicolons, braces)
- **Missing Tokens**: Insert synthetic tokens, continue parsing
- **Declaration Errors**: Skip to next declaration or statement boundary

### Semantic Recovery
- **Undefined Symbols**: Create error entries, continue analysis
- **Type Errors**: Use error types, propagate through expressions
- **Scope Errors**: Maintain scope stack, report violations

## Error Reporting System

### Diagnostic Engine
```rust
/// Central diagnostic collection and reporting
pub struct DiagnosticEngine {
    errors: Vec<Diagnostic>,
    warnings: Vec<Diagnostic>,
    notes: Vec<Diagnostic>,
}

/// Individual diagnostic with rich context
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub location: SourceSpan,
    pub code: Option<String>, // Error code like "E001"
    pub hints: Vec<String>, // Suggestions for fixing
    pub related: Vec<SourceSpan>, // Related locations
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Note,
}
```

### Error Formatting with annotate_snippets
```rust
/// Configurable error formatter using annotate_snippets
pub struct ErrorFormatter {
    pub show_source: bool,
    pub show_hints: bool,
    pub use_colors: bool,
    pub max_context: usize,
}

impl ErrorFormatter {
    /// Format a single diagnostic with rich source code context
    pub fn format_diagnostic(&self, diag: &Diagnostic, source_manager: &SourceManager) -> String {
        let level_str = match diag.level {
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
            DiagnosticLevel::Note => "note",
        };

        let mut result = format!("{}: {}", level_str, diag.message);

        // Add source location if available
        if let Some(file_info) = source_manager.get_file_info(diag.location.source_id()) {
            if let Some((line, col)) = source_manager.get_line_column(diag.location.start) {
                result.push_str(&format!(" at {}:{}:{}", file_info.path.display(), line, col));
            }
        }

        // Add hints if enabled
        if self.show_hints && !diag.hints.is_empty() {
            for hint in &diag.hints {
                result.push_str(&format!("\n  hint: {}", hint));
            }
        }

        // Add source code snippet if enabled
        if self.show_source {
            let source_text = source_manager.get_source_text(diag.location);
            result.push_str(&format!("\n  |\n  | {}\n  |", source_text.replace('\n', "\n  | ")));
        }

        result
    }
}
```

## Integration with Compiler Pipeline

### Error Collection
Each phase contributes to the global diagnostic collection:

1. **Preprocessor**: Include path resolution, macro validation
2. **Lexer**: Token validity, encoding issues
3. **Parser**: Syntax correctness, grammar violations
4. **Semantic**: Type safety, symbol resolution, scope rules
5. **Dumper**: Output generation issues

### Error Propagation
- **Non-blocking**: Errors don't stop compilation unless fatal
- **Accumulation**: All errors collected and reported together
- **Context Preservation**: Source locations maintained throughout pipeline
- **Cross-phase References**: Errors can reference locations from earlier phases

### IDE Integration
- **Structured Output**: JSON format available for tools
- **Source Maps**: Precise location mapping for editors
- **Error Codes**: Standardized codes for tool integration
- **Recovery Hints**: Suggestions for common error patterns