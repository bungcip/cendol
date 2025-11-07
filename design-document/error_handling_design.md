# Error Handling Strategy Design Document

## Error Types

```rust
/// Main compiler error enum
#[derive(Debug, thiserror::Error)]
pub enum CompilerError {
    #[error("Preprocessor error: {0}")]
    Preprocessor(#[from] PreprocessorError),
    #[error("Lexer error: {0}")]
    Lexer(#[from] LexerError),
    #[error("Parser error: {0}")]
    Parser(#[from] ParserError),
    #[error("Semantic error: {0}")]
    Semantic(#[from] SemanticError),
    #[error("System error: {0}")]
    System(#[from] SystemError),
}

/// Preprocessor errors
pub enum PreprocessorError {
    MacroRedefinition { name: Symbol, first_def: SourceSpan, second_def: SourceSpan },
    UndefinedMacro { name: Symbol, location: SourceSpan },
    IncludeFileNotFound { path: String, location: SourceSpan },
    RecursiveInclude { file: SourceId, location: SourceSpan },
    InvalidPragma { directive: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Lexer errors
pub enum LexerError {
    InvalidCharacter { ch: char, location: SourceSpan },
    UnterminatedString { location: SourceSpan },
    UnterminatedComment { location: SourceSpan },
    InvalidNumber { text: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Parser errors
pub enum ParserError {
    UnexpectedToken { expected: Vec<TokenKind>, found: Token, location: SourceSpan },
    MissingToken { expected: TokenKind, location: SourceSpan },
    SyntaxError { message: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Parser warnings
pub enum ParseWarning {
    /// Warning for unused labels, etc.
    UnusedLabel { name: Symbol, location: SourceSpan },
    /// Warning for implicit function declarations (C90 compatibility)
    ImplicitFunctionDeclaration { name: Symbol, location: SourceSpan },
    /// Warning for deprecated features
    DeprecatedFeature { message: String, location: SourceSpan },
    // ... more variants
}

/// Semantic warnings
pub enum SemanticWarning {
    /// Warning for unused variables, functions, or labels
    UnusedDeclaration { name: Symbol, location: SourceSpan },
    /// Warning for implicit type conversions that might lead to data loss
    ImplicitConversion { from_type: String, to_type: String, location: SourceSpan },
    /// Warning for unreachable code
    UnreachableCode { location: SourceSpan },
    /// Warning for deprecated features or constructs
    DeprecatedFeature { message: String, location: SourceSpan },
    // ... more variants
}

/// Semantic errors
pub enum SemanticError {
    UndeclaredIdentifier { name: Symbol, location: SourceSpan },
    Redefinition { name: Symbol, first_def: SourceSpan, second_def: SourceSpan },
    TypeMismatch { expected: String, found: String, location: SourceSpan },
    IncompleteType { name: Symbol, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}
```

## Error Recovery

1. **Pratt parser error recovery** - stop at minimum binding power
2. **Declaration context recovery** - reset to neutral declaration state
3. **Synchronization points** to resume parsing (semicolons, braces)
4. **Error symbol insertion** to continue processing
5. **Incremental error reporting** to show all errors
6. **Context preservation** for better error messages

## Error Reporting

```rust
/// Error context for better error messages
pub struct ErrorContext {
    pub current_function: Option<Symbol>,
    pub current_file: SourceId,
    pub current_line: u32,
    pub stack_trace: Vec<SourceLocation>,
}

/// Error formatter
pub struct ErrorFormatter {
    pub show_code_snippets: bool,
    pub show_stack_trace: bool,
    pub use_colors: bool,
    pub max_context_lines: usize,
}