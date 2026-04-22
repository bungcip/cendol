# Abstract Syntax Tree (AST) Design

## Overview

Cendol uses a unique Two-Stage AST architecture, optimized for both memory efficiency and cache locality. All AST nodes are stored in contiguous vectors and referenced by compact, 32-bit indices.

## The Two-Stage Approach

### 1. Syntactic AST (`ParsedAst`)
Produced directly by the parser.
- **Goal**: Rapidly capture the source structure without semantic overhead.
- **Nodes**: `ParsedNode`.
- **References**: `ParsedNodeRef`.
- **Properties**: Purely syntactic; identifiers are just names (`NameId`), and types are just syntactic specifiers.

### 2. Semantic AST (`Ast`)
Produced by the lowering phase.
- **Goal**: Represent the program in a form ready for type analysis and codegen.
- **Nodes**: `NodeKind`.
- **References**: `NodeRef`.
- **Properties**: Analyzed and resolved. Identifiers carry a `SymbolRef`. Nodes are linked to a specific scope.

## Flattened Storage

To avoid the performance penalties of traditional pointer-heavy trees (fragmented allocations, cache misses), Cendol uses "Side Tables":

| Feature | Implementation |
| :--- | :--- |
| **Node Kinds** | Contiguous `Vec<NodeKind>` |
| **Source Spans** | Contiguous `Vec<SourceSpan>` |
| **Semantic Info** | Contiguous `Vec<Option<QualType>>` (Parallel to Node kinds) |

This layout ensures that traversing the AST (which often requires checking only the kind or type) is extremely fast.

## Node Construction

Nodes in Cendol are designed to be small and `Copy`. Large data structures (like those representing an `If` statement's multiple branches) are stored in specialized data structs referenced by the `NodeKind`.

### Example: Binary Operation
In a traditional tree:
```rust
struct BinaryOp {
    left: Box<Node>,
    right: Box<Node>,
    op: OpKind,
    resolved_type: Type,
}
```

In Cendol's `Ast`:
```rust
enum NodeKind {
    BinaryOp(BinaryOpData),
    // ...
}

struct BinaryOpData {
    left: NodeRef,
    right: NodeRef,
    op: BinaryOpKind,
}
```
The `resolved_type` is stored in the `SemanticInfo` side table.

## Navigation and Modification

- **Children**: Accessed via `NodeRef` indices.
- **Dynamic Growth**: Flattened vectors can grow dynamically, though the driver typically pre-allocates for large files.
- **Immutability**: Once a phase finishes (e.g., Lowering), the AST nodes are generally immutable, but side-tables (`SemanticInfo`) can be populated incrementally.