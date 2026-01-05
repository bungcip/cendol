# Abstract Syntax Tree (AST) Design

## Overview

The AST design for Cendol follows a flattened storage approach optimized for cache performance and memory efficiency. All AST nodes are stored in contiguous vectors with index-based references instead of pointers. The AST serves as an intermediate representation between parsing and semantic analysis, with semantic information attached after type resolution.

## Key Design Principles

1. **Flattened Storage**: All nodes stored in `Vec<Node>` for cache-friendly access
2. **Index-based References**: Use `NodeRef` (NonZeroU32) instead of pointers
3. **Packed Data Structures**: Minimize memory footprint with compact representations
4. **Interior Mutability**: Use `Cell` for symbol resolution without mutable access
5. **Semantic Side Tables**: Separate semantic information stored in parallel vectors
6. **Parser-to-Semantic Transition**: AST nodes transform from parser-specific to semantic nodes

## AST Structure

The AST is composed of:

- `Ast` struct: Main container with flattened storage
- `Node` struct: Individual AST node with `NodeKind` and source span
- `NodeKind` enum: All possible AST node types
- `NodeRef` type: Index-based reference to nodes
- `ParsedTypeArena`: Storage for syntactic type representations
- `SemanticInfo`: Side table with resolved types, conversions, and value categories

## Node Design

Each node is stored as a `Node` struct containing:
- `kind`: The `NodeKind` enum variant
- `span`: Source location information

The `NodeKind` enum contains all possible AST node types including:

### Literals
- `LiteralInt(i64)`: Parsed integer literal value
- `LiteralFloat(f64)`: Parsed float literal value
- `LiteralString(NameId)`: Interned string literal
- `LiteralChar(u8)`: Character constant value

### Expressions
- `Ident(NameId, Cell<Option<SymbolRef>>)`: Identifier with resolved symbol
- `UnaryOp(UnaryOp, NodeRef)`: Unary operation
- `BinaryOp(BinaryOp, NodeRef, NodeRef)`: Binary operation
- `TernaryOp(NodeRef, NodeRef, NodeRef)`: Conditional expression
- `FunctionCall(NodeRef, Vec<NodeRef>)`: Function call with arguments
- `MemberAccess(NodeRef, NameId, bool)`: Member access with arrow flag
- `IndexAccess(NodeRef, NodeRef)`: Array indexing
- `Cast(QualType, NodeRef)`: Type cast with resolved type
- `SizeOfExpr(NodeRef)`: sizeof with expression
- `SizeOfType(QualType)`: sizeof with type
- `AlignOf(QualType)`: _Alignof with resolved type

### Parser-specific Nodes (Transformed by Symbol Resolver)
- `ParsedCast(ParsedType, NodeRef)`: Parser cast node
- `ParsedSizeOfType(ParsedType)`: Parser sizeof type node
- `ParsedCompoundLiteral(ParsedType, NodeRef)`: Parser compound literal
- `ParsedAlignOf(ParsedType)`: Parser alignof node
- `ParsedGenericSelection(...)`: Parser generic selection

### Statements
- `CompoundStatement(Vec<NodeRef>)`: Block of statements
- `If(IfStmt)`: If statement with condition and branches
- `While(WhileStmt)`: While loop
- `For(ForStmt)`: For loop with init, condition, increment
- `Return(Option<NodeRef>)`: Return statement
- `Goto(NameId, Cell<Option<SymbolRef>>)`: Goto with resolved label
- `Label(NameId, NodeRef, Cell<Option<SymbolRef>>)`: Label with resolved symbol
- `Switch(...)`: Switch statement
- `ExpressionStatement(Option<NodeRef>)`: Expression as statement

### Declarations and Definitions
- `Declaration(DeclarationData)`: Variable declaration
- `FunctionDef(FunctionDefData)`: Function definition
- `VarDecl(VarDeclData)`: Variable declaration with resolved type
- `FunctionDecl(FunctionDeclData)`: Function declaration
- `TypedefDecl(TypedefDeclData)`: Typedef declaration
- `RecordDecl(RecordDeclData)`: Struct/union declaration
- `EnumDecl(EnumDeclData)`: Enum declaration

## Type System Integration

The AST integrates with the semantic type system through:

### Parsed Types vs Semantic Types
- `ParsedType`: Syntactic type representation during parsing
- `QualType`: Semantic type with qualifiers after resolution
- `ParsedTypeArena`: Storage for syntactic type representations

### Semantic Information Side Table
- `SemanticInfo` struct: Parallel vectors indexed by node index
- `types`: Resolved types for each node (Vec<Option<QualType>>)
- `conversions`: Implicit conversions for each node
- `value_categories`: LValue/RValue categorization

### Symbol Resolution
- `Ident` nodes contain `Cell<Option<SymbolRef>>` for resolved symbols
- `Goto` and `Label` nodes have resolved symbol references
- Symbol resolution occurs during semantic analysis phases

## AST Lifecycle

1. **Parsing Phase**: AST populated with parser-specific nodes and `ParsedType`
2. **Symbol Resolution**: Parser-specific nodes transformed to semantic nodes
3. **Name Resolution**: Identifiers resolved to symbol table entries
4. **Semantic Analysis**: Types resolved and semantic information attached
5. **MIR Generation**: AST converted to typed MIR representation

## Memory Layout

The flattened storage provides:
- Cache-friendly sequential access to AST nodes
- Reduced memory fragmentation
- Efficient iteration over all nodes
- Compact representation with index-based references