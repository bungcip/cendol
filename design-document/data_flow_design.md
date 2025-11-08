# Data Flow and Integration Design Document

## Compiler Pipeline Overview

The Cendol compiler follows a traditional multi-phase architecture with clear data flow between phases. Each phase processes input from the previous phase and produces structured output for the next phase.

```mermaid
graph TD
    Source[Source Files] --> Preprocessor
    Preprocessor --> PPTokenStream[PPToken Stream]
    PPTokenStream --> Lexer
    Lexer --> TokenStream[Token Stream]
    TokenStream --> Parser
    Parser --> FlattenedAST[Flattened AST]
    FlattenedAST --> SemanticAnalyzer[Semantic Analysis]
    SemanticAnalyzer --> AnnotatedAST[Annotated AST + Symbol Table]
    AnnotatedAST --> ASTDumper[AST Dumper]
    ASTDumper --> HTML[HTML Output]
```

## Phase Inputs and Outputs

### Preprocessor Phase
**Input:**
- Source files and include paths
- Compiler configuration (macros, feature flags)

**Output:**
- `PPToken` stream with preprocessing directives resolved
- Source location mappings preserved
- Built-in macros initialized

### Lexer Phase
**Input:**
- `PPToken` stream from preprocessor
- Source manager for location tracking

**Output:**
- `Token` stream with keywords pre-interned
- Symbol table with global symbol interning
- Source spans for error reporting

### Parser Phase
**Input:**
- `Token` stream from lexer
- Diagnostic engine for error reporting

**Output:**
- Flattened AST (`Ast` struct with contiguous node storage)
- Initial symbol table with declarations
- Parse errors and warnings

### Semantic Analysis Phase
**Input:**
- Flattened AST from parser
- Symbol table from parser
- Type system definitions

**Output:**
- Annotated AST with resolved types and symbols
- Complete symbol table with all bindings
- Type table with canonicalized types
- Semantic errors and warnings

### AST Dumper Phase
**Input:**
- Annotated AST and symbol table
- Source manager for code snippets
- Dump configuration

**Output:**
- Interactive HTML visualization
- Cross-referenced tables (symbols, types, scopes)
- Source code integration

## Key Data Structures

```rust
/// Global symbol interning (from symbol_table crate)
pub type Symbol = symbol_table::GlobalSymbol;

/// Source location tracking (imported from source_manager)
pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};

/// Flattened AST storage
pub struct Ast {
    pub nodes: Vec<Node>,
    pub types: Vec<Type>,
    pub symbol_entries: Vec<SymbolEntry>,
    pub initializers: Vec<Initializer>,
}

/// Token structures
pub struct PPToken { /* Preprocessor tokens */ }
pub struct Token { /* Lexer tokens with pre-interned keywords */ }

/// Analysis results
pub struct SemanticOutput {
    pub errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
}
```

## Memory Management Strategy

- **Arena Allocation**: AST nodes allocated in bump allocator for cache efficiency
- **Global Symbol Interning**: Identifiers interned globally to avoid duplication
- **Flattened Storage**: All AST data in contiguous vectors for spatial locality
- **Index-based References**: `NodeRef`, `TypeRef`, `SymbolEntryRef` for efficient access

## Error Propagation

Each phase can produce errors that are collected and reported:

1. **Preprocessor**: Include errors, macro definition issues
2. **Lexer**: Invalid tokens, encoding problems
3. **Parser**: Syntax errors, missing tokens
4. **Semantic**: Type errors, undefined symbols, scope violations
5. **Dumper**: Output generation issues

Errors include source locations for precise reporting and IDE integration.