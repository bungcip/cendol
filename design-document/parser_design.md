# Parser Design

## Overview

The parser converts a lexical token stream into a flattened Abstract Syntax Tree (AST) according to C11 grammar rules. It uses a recursive descent approach with Pratt parsing for expressions, and includes sophisticated disambiguation mechanisms for C's complex grammar.

## Key Responsibilities

- **Syntax Analysis**: Parse tokens according to C11 grammar with proper operator precedence
- **AST Construction**: Build a syntactic `ParsedAst` from tokens with index-based references.

## Implementation Approach

The parser produces a `ParsedAst`, which is a purely syntactic representation of the C code. This tree is then lowered into a semantic `Ast` in the next phase.

### Recursive Descent for Statements and Declarations
- Top-down parsing for control flow and declaration constructs.
- Specialized handling for C's complex declarator syntax.
- Disambiguation between variable declarations and function definitions.

### Pratt Parsing for Expressions
- Handles all C11 operators with correct precedence and associativity.
- Uses `BindingPower` to manage operator precedence.
- Efficiently handles prefix, infix, and postfix operators.

## Core Components

### Parser Structure
- `Parser` struct: Orchestrates parsing, managing tokens from the `Lexer`.
- `ParsedAst`: Contiguous storage for `ParsedNode`s.
- `TypeDefContext`: Tracks typedefs to resolve the C "typedef name" ambiguity.

### Disambiguation
C's grammar is famously ambiguous regarding identifiers vs. type names. The `Parser` uses `TypeDefContext` to track active typedefs and distinguish between declarations and expressions using lookahead and context-sensitive checks.

## Error Handling

The parser implements robust error recovery:
- **Synchronization**: Skips tokens until a safe point (like a semicolon or closing brace) after an error.
- **Diagnostic Reporting**: Leverages the `DiagnosticEngine` to report multiple errors in a single pass.