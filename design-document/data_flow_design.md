# Data Flow and Integration

## Overview

This document describes how data flows between different phases of the compiler pipeline. It covers the interfaces between phases and the data structures used for communication. The compiler follows a multi-phase architecture with clear data boundaries between each phase.

## Phase Interfaces

The compiler phases communicate through well-defined interfaces:

### 1. Preprocessor → Lexer
- **Input**: `Vec<PPToken>` (preprocessing token stream)
- **Output**: `Vec<Token>` (lexical token stream)
- **Data Transformation**: Converts preprocessing tokens to lexical tokens, performs string literal concatenation, keyword recognition, and literal parsing

### 2. Lexer → Parser
- **Input**: `&[Token]` (token slice)
- **Output**: `Ast` (flattened Abstract Syntax Tree)
- **Data Transformation**: Parses token stream into structured AST with index-based references

### 3. Parser → Symbol Resolver
- **Input**: `Ast` (raw AST with parser-specific nodes)
- **Output**: `Ast` (transformed AST with semantic nodes), `SymbolTable`, `TypeRegistry`
- **Data Transformation**: Transforms parser-specific nodes to semantic nodes, establishes scopes, builds symbol table

### 4. Symbol Resolver → Name Resolver
- **Input**: `Ast` (transformed AST), `SymbolTable`
- **Output**: `Ast` (with resolved symbol references)
- **Data Transformation**: Resolves identifier names to symbol table entries, validates scoping rules

### 5. Name Resolver → Semantic Analyzer
- **Input**: `Ast` (with resolved symbols), `SymbolTable`, `TypeRegistry`
- **Output**: `Ast` (with semantic annotations), `SemanticInfo` (side table)
- **Data Transformation**: Performs type checking, implicit conversion analysis, value categorization

### 6. Semantic Analyzer → MIR Generation
- **Input**: `Ast` (fully annotated), `SymbolTable`, `TypeRegistry`
- **Output**: `SemaOutput` (complete MIR data structures)
- **Data Transformation**: Converts AST to typed MIR representation with explicit control flow

### 7. MIR Generation → Code Generation
- **Input**: `SemaOutput` (MIR data structures)
- **Output**: `ClifOutput` (Cranelift IR or object file)
- **Data Transformation**: Maps MIR constructs to Cranelift instructions, generates target code

## Data Structures

### PPToken (Preprocessing Token)
- Represents tokens after preprocessing (macro expansion, include resolution)
- Contains raw text and location information
- Used as input to the lexer

### Token (Lexical Token)
- Represents syntactic elements of C11 (keywords, identifiers, literals, operators)
- Contains token kind and source span
- Used as input to the parser

### Ast (Abstract Syntax Tree)
- Flattened storage of AST nodes in contiguous vectors
- Uses `NodeRef` (index-based references) instead of pointers
- Contains `Vec<Node>` for AST nodes and `ParsedTypeArena` for syntactic types
- Augmented with semantic information after analysis phases

### SymbolTable
- Flattened storage of symbol entries with hierarchical scope management
- Uses `SymbolRef` (index-based references) for efficient access
- Contains mappings between names and declarations

### TypeRegistry
- Manages canonical types with flattened storage
- Provides type interning and comparison
- Uses `TypeRef` (index-based references)

### SemanticInfo
- Side table with parallel vectors indexed by node index
- Contains resolved types, implicit conversions, and value categories
- Attached to AST after semantic analysis

### SemaOutput
- Complete MIR data structures including functions, blocks, locals, globals, types, and constants
- Contains all information needed for code generation
- Flattened storage with index-based references

## Error Handling in Data Flow

Each phase can produce diagnostics that are accumulated and reported:

- **DiagnosticEngine**: Centralized diagnostic collection across all phases
- **Non-blocking compilation**: Phases continue despite errors to provide comprehensive diagnostics
- **Phase-specific error recovery**: Each phase has appropriate recovery strategies
- **Rich error reporting**: Detailed error messages with source location information

## Memory Management

The compiler uses efficient memory management strategies:

- **Flattened storage**: All major data structures use contiguous vectors for cache efficiency
- **Index-based references**: Eliminate pointer indirection and improve cache locality
- **Arena allocation**: Efficient allocation patterns for AST and other structures
- **Symbol interning**: Global symbol table for memory efficiency and fast comparison

## Pipeline Coordination

The `CompilerDriver` orchestrates the entire pipeline:

- **Phase execution**: Manages execution of each phase in sequence
- **Data passing**: Coordinates data flow between phases
- **Error propagation**: Handles error conditions and reporting
- **Output generation**: Manages final output based on compilation goals
- **Stop-after control**: Allows stopping compilation at specific phases for debugging