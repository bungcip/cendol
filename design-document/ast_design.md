# Abstract Syntax Tree (AST) Design

## Overview

The AST design for Cendol follows a two-stage approach:
1.  **Syntactic AST (`ParsedAst`)**: A direct representation of the source code produced by the parser.
2.  **Semantic AST (`Ast`)**: A lowered, type-resolved representation used for analysis and code generation.

Both trees utilize a flattened storage approach optimized for cache performance and memory efficiency, using index-based references.

## Key Design Principles

1.  **Two-Stage Representation**: Separation of concerns between parsing (syntax) and analysis (semantics).
2.  **Flattened Storage**: All nodes stored in contiguous vectors (`Vec<NodeKind>`, `Vec<ParsedNodeKind>`) for cache-friendly access.
3.  **Index-based References**: Use `NodeRef` / `ParsedNodeRef` (NonZeroU32) instead of pointers.
4.  **Packed Data Structures**: Minimize memory footprint with compact representations.
5.  **Semantic Side Tables**: Semantic information (types, value categories) stored in `SemanticInfo` for the `Ast`.

## AST Structure

### Syntactic AST (`ParsedAst`)

Holds the raw output of the parser.
-   `ParsedAst` struct: Container with `nodes` and `parsed_types`.
-   `ParsedNodeKind` enum: Variants representing syntactic constructs (e.g., `Declaration`, `FunctionDef`).
-   `ParsedTypeArena`: Storage for syntactic type representations (`ParsedType`).

### Semantic AST (`Ast`)

Holds the analyzed and resolved program structure.
-   `Ast` struct: Container with `kinds` (nodes), `spans`, and optional `semantic_info`.
-   `NodeKind` enum: Variants representing semantic constructs (e.g., `VarDecl`, `BinaryOp` with resolved behavior).
-   `SemanticInfo`: Side table containing resolved `QualType`s, implicit conversions, and value categories.

## Node Design

### `NodeKind` (Semantic Nodes)

The `NodeKind` enum represents semantically resolved constructs. Key aspects include:
- **Expressions**: `Ident`, `UnaryOp`, `BinaryOp`, `TernaryOp`, `Cast`, `SizeOfExpr`, `ImplicitCast`, `GenericSelection`, `FunctionCall`.
- **Statements**: `CompoundStatement`, `If`, `While`, `DoWhile`, `For`, `Return`, `Break`, `Continue`, `Goto`, `Label`, `Switch`, `Case`, `Default`.
- **Declarations**: `VarDecl`, `FunctionDecl`, `TypedefDecl`, `RecordDecl`, `FieldDecl`, `EnumDecl`, `EnumMember`, `Function`, `Param`.
- **Infrastructure**: `TranslationUnit`, `InitializerList`, `InitializerItem`, `Designator`, `Dummy`.

Large variants use auxiliary data structures (e.g., `FunctionData`, `IfStmt`) to keep `NodeKind` compact and cache-friendly.

### `ParsedNodeKind` (Syntactic Nodes)

`ParsedNodeKind` is purely syntactic and lacks semantic resolution:
- **Declarations**: Uses generic `Declaration(ParsedDeclarationData)` and `FunctionDef(ParsedFunctionDefData)` instead of specific semantic variants.
- **Types**: Uses `ParsedType` (syntactic representation) instead of `QualType`.
- **Expressions**: Standard C operators, but without symbol or type resolution (e.g., `Ident(NameId)`).

## Memory Layout

- **Contiguous Storage**: Both `Ast` and `ParsedAst` use `Vec<NodeKind>` and `Vec<ParsedNodeKind>` for optimal cache performance.
- **Index-based References**: `NodeRef` and `ParsedNodeRef` are `NonZeroU32` wrappers that index into these vectors.
- **Compactness**: Shared data structures across nodes are boxed or stored as indices to minimize `NodeKind` size.
- **Side Tables**: Any data that doesn't fit the uniform node structure is stored in side tables (e.g., `SemanticInfo`).