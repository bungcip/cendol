# Parser Design

## Overview

The parser converts a lexical token stream into a flattened Abstract Syntax Tree (AST) according to C11 grammar rules. It uses a recursive descent approach with Pratt parsing for expressions, and includes sophisticated disambiguation mechanisms for C's complex grammar.

## Key Responsibilities

- **Syntax Analysis**: Parse tokens according to C11 grammar with proper operator precedence
- **AST Construction**: Build flattened AST nodes from tokens with index-based references
- **Error Recovery**: Handle syntax errors gracefully with synchronization points
- **Expression Parsing**: Use Pratt parsing for operator precedence and associativity
- **Declaration Disambiguation**: Handle the C declaration/expression ambiguity
- **Type Name Recognition**: Distinguish between typedef names and identifiers in context

## Implementation Approach

The parser uses:

### Recursive Descent for Statements and Declarations
- Top-down parsing for control flow and declaration constructs
- Dedicated functions for each grammar production
- Proper handling of C's complex declaration syntax

### Pratt Parsing for Expressions
- Handles all C11 operators with correct precedence and associativity
- Dynamic binding power system for flexible operator handling
- Proper handling of unary vs binary operators with same token

### Type Context Management
- `TypeDefContext` for tracking typedef names and disambiguation
- Dynamic addition of typedef names during parsing
- Context-sensitive parsing for declaration vs expression ambiguity

### Error Recovery
- Synchronization points at statement boundaries
- Recovery through unmatched braces and parentheses
- Continuation after errors to provide comprehensive diagnostics

## Core Components

### Parser Structure
- `Parser` struct: Main parser state with token stream, AST builder, and diagnostic engine
- `TypeDefContext`: Tracks typedef names for disambiguation
- `ParserState`: State management for transactional parsing

### Expression Parsing
- Pratt parser with binding power system
- Support for all C11 operators with correct precedence
- Unary and binary operator handling
- Cast expression detection and parsing

### Declaration Parsing
- Complex declarator parsing for C's type system
- Support for pointers, arrays, functions, and combinations
- Parameter list parsing with proper scoping
- Initialization handling

### Statement Parsing
- Control flow statements (if, while, for, switch, etc.)
- Compound statements with proper scoping
- Jump statements (return, break, continue, goto)
- Expression statements

## Disambiguation Strategies

### Declaration vs Expression
- Context-sensitive parsing using `TypeDefContext`
- Lookahead to distinguish declarations from expressions
- Proper handling of type names vs identifiers

### Cast Expression Detection
- Special handling for cast expressions in parentheses
- Type name recognition in parenthetical contexts
- Distinction from grouping parentheses

## AST Integration

The parser directly builds the flattened AST:
- Nodes stored in contiguous vectors for cache efficiency
- Index-based references instead of pointers
- Source location tracking for all AST nodes
- Immediate attachment of semantic information where possible

## Error Handling

### Recovery Strategy
- Synchronization at statement boundaries (semicolons, braces)
- Recovery through unmatched control flow constructs
- Continuation after errors to provide comprehensive diagnostics

### Diagnostic Reporting
- Rich error messages with source location information
- Expected vs found token reporting
- Context-sensitive error messages
- Non-blocking error handling

## Performance Optimizations

- Flattened AST construction during parsing
- Efficient token lookahead and consumption
- Optimized keyword and operator recognition
- Minimal allocations during parsing
- Cache-friendly AST node storage