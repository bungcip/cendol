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

The `NodeKind` enum in `Ast` represents the semantically valid constructs. Key variants include:

#### Literals
-   `Literal(Literal)`: Wraps a `Literal` enum (Integer, Float, String, Char).

#### Expressions
-   `Ident(NameId, SymbolRef)`: Identifier with resolved symbol reference.
-   `UnaryOp(UnaryOp, NodeRef)`: Unary operation.
-   `BinaryOp(BinaryOp, NodeRef, NodeRef)`: Binary operation.
-   `TernaryOp(NodeRef, NodeRef, NodeRef)`: Conditional expression.
-   `FunctionCall(CallExpr)`: Function call with arguments.
-   `MemberAccess(NodeRef, NameId, bool)`: Member access.
-   `IndexAccess(NodeRef, NodeRef)`: Array indexing.
-   `Cast(QualType, NodeRef)`: Explicit cast with resolved type.
-   `SizeOfExpr(NodeRef)`: `sizeof` expression.
-   `SizeOfType(QualType)`: `sizeof` type.
-   `AlignOf(QualType)`: `_Alignof` type.
-   `GnuStatementExpression(NodeRef, NodeRef)`: GNU statement expression.

#### Statements
-   `CompoundStatement(CompoundStmtData)`: Block with scope.
-   `If(IfStmt)`: If statement.
-   `While(WhileStmt)`: While loop.
-   `DoWhile(NodeRef, NodeRef)`: Do-while loop.
-   `For(ForStmt)`: For loop with scope.
-   `Return(Option<NodeRef>)`: Return statement.
-   `Goto(NameId, SymbolRef)`: Goto with resolved symbol.
-   `Label(NameId, NodeRef, SymbolRef)`: Label with resolved symbol.
-   `Switch(NodeRef, NodeRef)`: Switch statement.
-   `Case`, `Default`, `CaseRange`: Switch cases.

#### Declarations (Semantic)
The semantic AST uses specific declaration nodes instead of generic `Declaration` nodes:
-   `VarDecl(VarDeclData)`: Variable declaration.
-   `FunctionDecl(FunctionDeclData)`: Function declaration.
-   `TypedefDecl(TypedefDeclData)`: Typedef definition.
-   `RecordDecl(RecordDeclData)`: Struct/Union definition.
-   `EnumDecl(EnumDeclData)`: Enum definition.
-   `Function(FunctionData)`: Complete function definition including body.

### `ParsedNodeKind` (Syntactic Nodes)

The `ParsedNodeKind` usually mirrors `NodeKind` but uses `ParsedNodeRef` and `ParsedType`. Differences include:
-   `Ident(NameId)`: No `SymbolRef`.
-   `Declaration(ParsedDeclarationData)`: Raw declaration specifiers and declarators.
-   `FunctionDef(ParsedFunctionDefData)`: Raw function definition.
-   `Cast(ParsedType, ParsedNodeRef)`: Cast with syntactic type.

## Type System Integration

-   **Parsed Types**: `ParsedType` represents what the user wrote (e.g., `int *`). Stored in `ParsedTypeArena`.
-   **Semantic Types**: `QualType` represents the canonical type (e.g., `pointer to integer`).
-   **Resolution**: During lowering from `ParsedAst` to `Ast`, `ParsedType`s are resolved to `QualType`s.
-   **Side Tables**: `Ast` stores `type` and `value_category` for every node in `SemanticInfo`, indexed by `NodeRef`.

## Memory Layout

-   Nodes are strictly ordered in `Vec`.
-   `NodeRef` and `ParsedNodeRef` are `NonZeroU32` indices.
-   Large data variants are boxed or stored in auxiliary structs (e.g., `FunctionData`, `IfStmt`) to keep `NodeKind` size uniform and small.