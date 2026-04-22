# Parser Design

## Overview

The Cendol parser consumes lexical tokens and constructs a `ParsedAst`. It is designed for high performance and strict C23 grammar compliance.

## Parsing Strategy

The parser uses a hybrid approach:
1. **Pratt Parsing (Top-Down Operator Precedence)**: Used for all expressions. This handles C's complex operator precedence (15+ levels) efficiently and with minimal recursion.
2. **Recursive Descent**: Used for statements, declarations, and high-level program structure.

## Core Responsibilities

- **Syntactic Validation**: Ensure the token stream follows C23 grammar rules.
- **Disambiguation**: Resolve the "typedef name" vs "identifier" ambiguity using a `TypeDefContext`.
- **AST Construction**: Populate the `ParsedAst` vectors with nodes and syntactic types.
- **Error Recovery**: Synchronize to statement/block boundaries after a syntax error to report multiple diagnostics.

## Disambiguation and Context

C grammar is famously context-sensitive. The parser maintains a `TypeDefContext` that tracks names currently defined as typedefs in the current scope. This allows the parser to determine if `A * B;` is a declaration of pointer `B` or a multiplication of `A` and `B`.

## Expression Parsing (Pratt)

Pratt parsing allows each operator to define its "binding power" and its own parsing function (`nud` for prefix, `led` for infix). This eliminates the need for deeply nested recursive functions for each precedence level (e.g., `parse_mult_expr`, `parse_add_expr`).

## Statement and Declaration Parsing

The parser follows a traditional recursive descent structure for high-level constructs:
- `parse_external_declaration` (Top level)
- `parse_statement` (Handles `if`, `while`, `for`, etc.)
- `parse_declaration` (Handles variable and type declarations)
- `parse_declarator` (Handles C's recursive declarator syntax)

## Handling C23 Features

The parser is updated for C23:
- Supports `static_assert` as a declaration and statement.
- Supports `nullptr`.
- Correctly parses the `: underlying_type` syntax for enumerations.
- Handles `[[...]]` attribute syntax at various positions (declarations, statements).