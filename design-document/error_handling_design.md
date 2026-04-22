# Error Handling Design

## Overview

Cendol aims for IDE-quality diagnostics. Errors are not fatal to the compiler process (it always attempts to continue), but they are fatal to the final artifact generation.

## The `DiagnosticEngine`

All errors, warnings, and notes are collected in the `DiagnosticEngine`.
- **Decoupled Reporting**: Phases report errors by pushing to the engine instead of returning `Result::Err`.
- **Rich Spans**: Errors are associated with a `SourceSpan`, allowing the engine to highlight the exact problematic code.
- **Support for Multi-file Diagnostics**: Can report errors that span across different files (e.g., a macro defined in a header but causing an error in the source).

## Error Levels

1. **Error**: A standard-violating construct. Prevents object code generation.
2. **Warning**: Legal but suspicious code (e.g., `-Wparentheses`, `-Wimplicit-conversion`).
3. **Note**: Additional context for an error (e.g., "previous definition was here").

## Non-Blocking Architecture

Phases are designed to recover from errors:
- **Parser**: After a syntax error, it skips tokens until the next semicolon or closing brace to resume parsing.
- **Lowering**: If a declaration is invalid, it may register a "poisoned" symbol to allow later code referencing that name to fail gracefully.
- **Analysis**: If an expression has a type error, it is assigned a "poison" type to prevent subsequent redundant errors from being reported on parent expressions.

## Visual Output

Cendol uses the `annotate-snippets` crate to render diagnostics.
- Provides clear code snippets.
- Highlights multiple spans (labels).
- Supports different colors/styles for errors vs. warnings.

## Internal Compiler Errors (ICE)

Unexpected states that signify bugs in Cendol itself are handled via `unreachable!` or `panic!`. These represent invariants that should never be violated if the compiler logic is correct.