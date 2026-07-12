# Cendol - C23 Compiler Driver Design Document

## Overview

The Cendol compiler driver orchestrates the entire compilation pipeline, from source file input through native code generation and linking. It provides a command-line interface using a custom parser that natively supports GCC/Clang-style single-dash long options and manages the transition between different data representations (Source -> PPToken -> Token -> ParsedAst -> Ast -> MIR -> Object).

## Responsibilities

- **CLI Interface**: Parse arguments and configure the compilation session.
- **Session Management**: Maintain the `DiagnosticEngine`, `SourceManager`, `SymbolTable`, and `TypeRegistry` throughout the compilation.
- **Pipeline Orchestration**: Execute phases in sequence, handling errors and stopping when necessary.
- **Artifact Generation**: Produce final outputs like object files, executables, or IR dumps.
- **Toolchain Integration**: Invoke the system linker (e.g., `clang`) to create final binaries.

## CLI Interface

The driver uses a custom parser to provide a GCC/Clang-like interface. Key options include:

- `-o <file>`: Specify output path.
- `-E`: Preprocess only.
- `-c`: Compile only (emit object file).
- `-I <dir>`: Add include search path.
- `-D <macro>`: Define preprocessor macro.
- `--std=<std>`: Select C standard (defaults to C23).

## Core Driver Session

The `CompilerDriver` (in `src/driver/compiler.rs`) acts as the state container for a single compilation run.

### Pipeline Flow

1.  **Initialize**: Load configuration and setup the `SourceManager`.
2.  **Preprocess**: Execute the `Preprocessor` to expand macros and handle directives.
3.  **Lex**: Convert `PPToken` stream into `Token` stream.
4.  **Parse**: Build a syntactic `ParsedAst`.
5.  **Lower**: Transform `ParsedAst` into a semantic `Ast`, populating symbols and types.
6.  **Analyze**: Perform type checking and side-table population (`SemanticInfo`).
7.  **MIR Gen**: Lower the analyzed `Ast` to `MirModule`.
8.  **Codegen**: Generate native code using the `ClifGen` (Cranelift) backend.
9.  **Link**: Invoke the system linker on generated object files and libraries.

## Error Handling

The driver monitors the `DiagnosticEngine` after each major phase. If errors are reported, the pipeline is typically halted before entering the next phase (e.g., if parsing fails, semantic analysis is skipped). This prevents "cascading" errors caused by invalid upstream data.

## Internal Workings

### Source Manager Interaction
The driver uses the `SourceManager` as the source of truth for all file content. It adds the main input file and any virtual buffers needed for built-in defines.

### Temporary File Management
During compilation and linking, the driver manages temporary object files, ensuring they are placed in appropriate directories (or current directory if `-c` is used) and cleaned up if they are intermediate artifacts.

### Linker Invocation
The driver identifies the host platform to determine the correct linker flags and system libraries. It typically shells out to `clang` to perform the final link step, leveraging its knowledge of system paths and CRT objects.