# Rust Environment and External Crates Design Document

## Rust Version and Edition

Cendol is developed using **Rust 2024 Edition**. This edition brings several new features, quality-of-life improvements, and performance enhancements that are leveraged throughout the compiler's codebase.

Key aspects of Rust 2024 Edition relevant to Cendol:
- **Improved Ergonomics**: Simplifications in syntax and common patterns.
- **Performance Enhancements**: Compiler optimizations and library improvements.
- **New Language Features**: Specific features introduced in this edition that may be utilized.

## External Crates

Cendol utilizes several external crates to streamline development, enhance functionality, and improve performance. Below is a list of key external crates and their purposes:

### 1. `clap`

- **Purpose**: Command-line argument parser.
- **Explanation**: Used by the compiler driver to define and parse command-line options provided by the user. It offers a declarative way to build robust and user-friendly CLIs.
- **Reference**: See [Compiler Driver Design](compiler_driver_design.md) for its usage in defining CLI options.

### 2. `bumpalo`

- **Purpose**: Fast arena allocator.
- **Explanation**: Essential for the AST design, `bumpalo` provides a highly efficient way to allocate AST nodes and other transient data structures in a contiguous memory region. This significantly improves cache locality and reduces allocation/deallocation overhead, crucial for compiler performance.
- **Reference**: See [Abstract Syntax Tree (AST) Design](ast_design.md) for details on arena allocation.

### 3. `hashbrown`

- **Purpose**: High-performance hash map implementation.
- **Explanation**: Used for symbol interning, type canonicalization, and other hash-map-intensive operations where performance is critical. `hashbrown` is a drop-in replacement for `std::collections::HashMap` but offers superior performance, especially in scenarios with many insertions and lookups, making it ideal for compiler data structures.
- **Reference**: Used internally for `StringInterner` in [Abstract Syntax Tree (AST) Design](ast_design.md), `macro_table` in [Preprocessor Design Document](preprocessor_design.md), `PrattTable` in [Parser Design Document](parser_design.md), and `SymbolTable` and `TypeTable` in [Semantic Analysis Phase](semantic_analysis_design.md).

### 4. `thiserror`

- **Purpose**: Derive macros for error types.
- **Explanation**: Simplifies the creation and management of custom error types, providing a consistent and ergonomic way to define the various `CompilerError` variants across different phases.
- **Reference**: See [Error Handling Strategy](error_handling_design.md) for its role in defining compiler errors.

### 5. `anyhow`

- **Purpose**: Flexible concrete error type.
- **Explanation**: Used for general-purpose error handling in application-level code (e.g., in `main.rs` or the compiler driver) where specific error types are not strictly necessary, providing a convenient `Result` type.

### 6. `log` and `env_logger`

- **Purpose**: Logging framework.
- **Explanation**: `log` provides a facade for logging, while `env_logger` is a popular implementation that allows configuring logging levels via environment variables. Used for debugging output and verbose modes.

### 7. `itertools`

- **Purpose**: Extra iterator adaptors.
- **Explanation**: Provides a rich set of utilities for working with iterators, which can simplify complex data processing tasks within the compiler phases.

### 8. `chrono`

- **Purpose**: Date and time library.
- **Explanation**: Used for expanding the `__DATE__` and `__TIME__` preprocessor macros, providing accurate and locale-aware date and time information during compilation.
- **Reference**: Relevant for the [Preprocessor Design Document](preprocessor_design.md).

### 9. `bitflags`

- **Purpose**: Macro to generate types for bit flags.
- **Explanation**: Used for compact storage of boolean flags in data structures, improving cache efficiency and memory usage.
- **Reference**: Used for `MacroFlags` and `PPTokenFlags` in [Preprocessor Design Document](preprocessor_design.md).

### 10. `target-lexicon`

- **Purpose**: Cross-platform target information.
- **Explanation**: Provides target triple parsing and platform-specific information needed for preprocessor target-dependent behavior.
- **Reference**: Used for `TargetTriple` in [Preprocessor Design Document](preprocessor_design.md).

### 11. `symbol_table`

- **Purpose**: Global symbol interning with thread-safe global symbol table.
- **Explanation**: Provides efficient string interning with global symbol table using the `global` feature. Enables fast symbol comparisons and memory-efficient storage of identifiers.
- **Reference**: Used for `GlobalSymbol` type aliased as `Symbol` throughout the compiler for identifier management.

### 12. `annotate_snippets`

- **Purpose**: Rich diagnostic error reporting with source code snippets.
- **Explanation**: Provides beautiful, annotated error messages with source code context, colors, and structured formatting. Enables IDE-quality error reporting with syntax highlighting and precise location indicators.
- **Reference**: Used in the error handling system for formatting diagnostics with source code snippets and contextual information.

### 11. `cranelift` (Future Integration)

- **Purpose**: Code generation backend.
- **Explanation**: In future phases, Cranelift will be used to generate machine code from an intermediate representation. It is a fast, secure, and portable code generator.
- **Reference**: Mentioned in [Compiler Driver Design](compiler_driver_design.md) and [main.md] as the chosen code generation backend.

## Referencing External Crates

When designing or implementing a new feature or phase, developers should refer to this document to understand the purpose and appropriate usage of these external crates. If a new external crate is introduced, it must be documented here with a clear explanation of its role.