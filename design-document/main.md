# Cendol - C11 Compiler Design Document

## Table of Contents
1. [Overview](#overview)
2. [Architecture Overview](#architecture-overview)
    2.1. [Compiler Driver Design](compiler_driver_design.md)
    2.2. [Rust Environment and External Crates](rust_environment_design.md)
3. [Preprocessor Phase](preprocessor_design.md)
4. [Lexer Phase](lexer_design.md)
5. [Parser Phase](parser_design.md)
6. [Abstract Syntax Tree (AST) Design](ast_design.md)
7. [Semantic Analysis Phase](semantic_analysis_design.md)
8. [AST Dumper Phase](ast_dumper_design.md)
9. [Data Flow and Integration](data_flow_design.md)
10. [Performance Considerations](performance_design.md)
11. [Error Handling Strategy](error_handling_design.md)

## Overview

This document outlines the design for Cendol, a high-performance C11 compiler written in Rust. The compiler follows a traditional multi-phase architecture optimized for performance, cache efficiency, and comprehensive C11 standard compliance, with a future focus on using Cranelift for code generation.

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
[Code Generation (Cranelift)] → Intermediate Representation (IR)
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