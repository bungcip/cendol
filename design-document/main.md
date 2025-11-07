# Cendol - C11 Compiler Design Document

## Table of Contents
1. [Overview](#overview)
2. [Architecture Overview](#architecture-overview)
    2.1. [Compiler Driver Design](compiler_driver_design.md)
3. [Preprocessor Phase](preprocessor_design.md)
4. [Lexer Phase](lexer_design.md)
5. [Parser Phase](parser_design.md)
6. [Abstract Syntax Tree (AST) Design](ast_design.md)
7. [Semantic Analysis Phase](#semantic-analysis-phase)
8. [AST Dumper Phase](ast_dumper_design.md)
9. [Data Flow and Integration](#data-flow-and-integration)
10. [Performance Considerations](#performance-considerations)
11. [Error Handling Strategy](#error-handling-strategy)

## Overview

This document outlines the design for Cendol, a high-performance C11 compiler written in Rust. The compiler follows a traditional multi-phase architecture optimized for performance, cache efficiency, and comprehensive C11 standard compliance.

### Design Goals
- **Performance**: Minimize memory allocations and maximize cache locality
- **Standards Compliance**: Full C11 support including all optional features
- **Modularity**: Clear separation of concerns between phases
- **Extensibility**: Easy to extend for future C standards and optimizations
- **Debuggability**: Comprehensive error reporting and debugging support

## Architecture Overview

```
Source Code (.c files)
    ↓
[Preprocessor] → Preprocessed Source
    ↓
[Lexer] → Token Stream
    ↓
[Parser] → AST
    ↓
[Semantic Analysis] → Annotated AST
    ↓
[AST Dumper] → Output (debug/logging)
```

### Key Design Decisions

1. **Arena Allocation**: All AST nodes allocated in arena for cache locality
2. **Symbol Interning**: String deduplication using integer IDs
3. **Source Location Tracking**: Packed source location for efficient span management
4. **Zero-Copy Parsing**: Minimize intermediate allocations
5. **Streaming Processing**: Process data in chunks to reduce memory pressure

## Preprocessor Phase

Refer to the [Preprocessor Design Document](preprocessor_design.md) for detailed information.

## Lexer Phase

Refer to the [Lexer Design Document](lexer_design.md) for detailed information.

## Parser Phase

Refer to the [Parser Design Document](parser_design.md) for detailed information.

## Semantic Analysis Phase

### Responsibilities
- Symbol table management and scope resolution
- Type checking and type equivalence
- Constant expression evaluation
- Declaration checking and validity
- _Static_assert evaluation
- _Generic selection resolution

### Data Structures

```rust
/// Symbol table entry
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind,
    pub type_info: Option<&'arena Type<'arena>>,
    pub storage_class: Option<StorageClass>,
    pub scope: ScopeId,
    pub definition_location: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
}

/// Symbol kinds
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
        initializer: Option<ConstantExpression>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: Vec<ParameterInfo>,
    },
    Typedef {
        underlying_type: &'arena Type<'arena>,
    },
    EnumConstant {
        value: Option<i64>,
    },
    Label {
        is_defined: bool,
        is_used: bool,
    },
    StructOrUnion {
        is_complete: bool,
        members: Option<Vec<MemberInfo>>,
        size: Option<usize>,
        alignment: Option<usize>,
    },
    Macro {
        definition: MacroDef,
        is_builtin: bool,
    },
}

/// Scope management
pub struct ScopeManager {
    scopes: Vec<Scope>,
    current_scope: ScopeId,
    global_scope: ScopeId,
    // For file scope variables
    translation_unit_scope: ScopeId,
}

/// Scope structure
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntry>,
    pub is_block_scope: bool,
    pub function_scope: Option<FunctionScopeId>,
}

/// Type representation (from AST design)
pub struct Type<'arena> {
    pub kind: TypeKind<'arena>,
    pub qualifiers: TypeQualifiers,
    pub size: Option<usize>,
    pub alignment: Option<usize>,
}
```

### Semantic Analysis Algorithm

1. **First pass**: Collect all declarations and build symbol table
2. **Second pass**: Complete type information and resolve forward references
3. **Third pass**: Check semantics and generate warnings/errors
4. **Fourth pass**: Final validation and optimization preparation

### Type System Features

- **Complete type checking** for C11 standard compliance
- **Atomic types** (_Atomic) with proper synchronization semantics
- **Complex types** (_Complex)
- **Alignment specifiers** (_Alignas)
- **Type qualifiers** (const, volatile, restrict, _Atomic)
- **Pointer arithmetic** validation
- **Function type** checking with parameter and return types
- **Array bounds** checking (flexible array members)

## AST Dumper Phase

### Responsibilities
- Visual representation of AST for debugging
- Multiple output formats (DOT, JSON, human-readable text)
- Symbol table visualization
- Type information display
- Performance profiling integration

### Implementation

```rust
/// AST dumper configuration
pub struct DumpConfig {
    pub format: OutputFormat,
    pub include_symbols: bool,
    pub include_types: bool,
    pub include_locations: bool,
    pub max_depth: Option<usize>,
    pub highlight_errors: bool,
}

/// Output formats
pub enum OutputFormat {
    HumanReadable,
    Json,
    Dot, // Graphviz format
    Xml,
}

/// AST dumping interface
pub trait AstDumper {
    fn dump_node(&self, node: &Node, config: &DumpConfig) -> String;
    fn dump_symbol_table(&self, table: &SymbolTable) -> String;
    fn dump_type_info(&self, type_info: &Type) -> String;
}

/// Human-readable formatter
pub struct HumanReadableDumper {
    indent_level: usize,
    line_number: u32,
}

/// JSON formatter
pub struct JsonDumper {
    pretty_print: bool,
}
```

## Data Flow and Integration

### Inter-Phase Communication

```
Preprocessor → [PreprocessedSource] → Lexer
                ↓
Lexer → [TokenStream] → Parser
                ↓
Parser → [AST] → SemanticAnalyzer
                ↓
SemanticAnalyzer → [AnnotatedAST] → ASTDumper
```

### Data Structures Between Phases

```rust
/// Preprocessor output
pub struct PreprocessedSource<'src> {
    pub text: &'src str,
    pub included_files: Vec<SourceFile>,
    pub macro_definitions: HashMap<Symbol, MacroDef>,
    pub line_directives: Vec<LineDirective>,
}

/// Lexer output
pub struct TokenStream<'src> {
    pub tokens: Vec<Token<'src>>,
    pub source_mapping: Vec<SourceMapping>,
    pub total_lines: u32,
}

/// Parser output
pub struct ParseResult<'arena> {
    pub ast: Option<&'arena Node<'arena>>,
    pub parse_errors: Vec<ParseError>,
    pub warnings: Vec<ParseWarning>,
    pub symbol_table: SymbolTable,
}

/// Semantic analysis result
pub struct SemanticResult<'arena> {
    pub annotated_ast: Option<&'arena Node<'arena>>,
    pub semantic_errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
    pub symbol_table: SymbolTable,
    pub type_table: TypeTable,
}
```

## Performance Considerations

### Memory Management

1. **Arena Allocation**: All AST nodes allocated in arena
2. **String Interning**: Reduce memory usage for repeated strings
3. **Zero-Copy Parsing**: Minimize intermediate allocations
4. **Lazy Evaluation**: Only compute when needed

### Cache Optimization

1. **Struct-of-Arrays** layout for repeated data
2. **Hot/Cold Splitting**: Separate frequently accessed from rarely accessed data
3. **Memory Prefetching**: Hint for predictable memory access patterns
4. **Data Locality**: Group related data structures

### Complexity Analysis

| Phase | Time Complexity | Space Complexity |
|-------|----------------|------------------|
| Preprocessing | O(n) | O(m) where m is macro count |
| Lexing | O(n) | O(1) |
| Parsing | O(n) | O(p) where p is precedence levels |
| Semantic Analysis | O(n) | O(s) where s is symbol count |
| AST Dumping | O(n) | O(1) |

## Error Handling Strategy

### Error Types

```rust
/// Comprehensive error types
pub enum CompilerError {
    Preprocessor(PreprocessorError),
    Lexer(LexerError),
    Parser(ParserError),
    Semantic(SemanticError),
    System(SystemError),
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

### Error Recovery

1. **Pratt parser error recovery** - stop at minimum binding power
2. **Declaration context recovery** - reset to neutral declaration state
3. **Synchronization points** to resume parsing (semicolons, braces)
4. **Error symbol insertion** to continue processing
5. **Incremental error reporting** to show all errors
6. **Context preservation** for better error messages

### Error Reporting

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
```

This design document provides a comprehensive foundation for building a high-performance C11 compiler in Rust. The architecture emphasizes performance, standards compliance, and maintainability while providing robust error handling and debugging capabilities.