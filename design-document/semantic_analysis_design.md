# Semantic Analysis Design

## Overview

Semantic analysis is a multi-phase process that checks the syntactically correct AST for semantic correctness and transforms it into a fully annotated form ready for MIR generation. This includes symbol resolution, type checking, scope management, and ensuring that the program follows the rules of the C language.

## Key Components

1. **Symbol Table**: Maintains mappings between identifiers and their declarations using flattened storage
2. **Type Registry**: Manages canonical types and type relationships
3. **Name Resolver**: Resolves identifiers to their symbol table entries
4. **Type Checker**: Validates type compatibility and performs type resolution
5. **Symbol Resolver**: Initial symbol collection and AST transformation
6. **AST-to-MIR Lowerer**: Converts annotated AST to typed MIR representation

## Multi-Phase Process

The semantic analysis process involves multiple distinct phases:

### 1. Semantic Lowering Phase
- Converts `ParsedAst` (parse tree) to `Ast` (semantic tree)
- Performs declaration lowering and symbol table construction
- Handles scope construction and symbol definition
- Resolves identifiers to symbol table entries
- Stores scope information directly on AST nodes

### 2. Semantic Analysis Phase
- Performs comprehensive type checking on the `Ast`
- Resolves expression types and validates compatibility
- Analyzes implicit conversions and value categories
- Validates all C constructs semantically
- Generates `SemanticInfo` side table

### 3. MIR Generation Phase
- Converts the fully annotated `Ast` (with `SemanticInfo`) to typed MIR
- Creates explicit control flow and memory operations
- Preserves comprehensive type information
- Validates MIR correctness before code generation

## Symbol Table Design

The symbol table uses flattened storage for efficiency:

- `SymbolTable`: Main container with `Vec<Symbol>` for flattened storage
- `SymbolRef`: Index-based reference to symbol entries
- `ScopeId`: Identifier for hierarchical scope management
- `SymbolKind`: Enum for different symbol types (Variable, Function, Typedef, etc.)

## Type System Integration

The semantic analysis integrates with the type system through:

- `TypeRegistry`: Manages canonical types with flattened storage
- `QualType`: Qualified types with type and qualifiers
- `TypeRef`: Index-based reference to types
- `TypeKind`: Enum for different type kinds (Int, Pointer, Array, etc.)

## Semantic Information Side Table

After semantic analysis, the AST is augmented with semantic information:

- `SemanticInfo`: Side table with parallel vectors indexed by node index
- `types`: Resolved types for each node (Vec<Option<QualType>>)
- `conversions`: Implicit conversions for each node
- `value_categories`: LValue/RValue categorization (Vec<ValueCategory>)

## Error Handling

Semantic analysis includes comprehensive error handling:

- Rich diagnostic reporting with source location information
- Non-blocking analysis that continues despite errors
- Detailed error messages with context
- Phase-specific error recovery strategies

## Validation

Multiple validation steps ensure semantic correctness:

- Symbol resolution validation
- Type compatibility validation
- Scope rule validation
- Implicit conversion validation
- LValue/RValue categorization validation

This multi-phase approach ensures that semantic analysis is both comprehensive and efficient, preparing the AST for MIR generation and code generation.