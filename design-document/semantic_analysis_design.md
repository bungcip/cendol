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

The semantic analysis process is split into two major phases, followed by MIR generation:

### 1. Semantic Lowering Phase
- **Entry point**: `visit_ast` in `lowering.rs`.
- **Goal**: Transform syntactic `ParsedAst` into semantic `Ast`.
- **Activities**:
    - Build `SymbolTable` and `TypeRegistry`.
    - Construct hierarchical `Scope` structure.
    - Resolve declarations (variables, functions, typedefs, types).
    - Map `ParsedNode`s to one or more `NodeRef`s in the semantic `Ast`.
- **Details**: See [semantic_lowering_design.md](file:///home/bungcip/cendol/design-document/semantic_lowering_design.md).

### 2. Semantic Analysis Phase
- **Entry point**: `visit_ast` in `analyzer.rs`.
- **Goal**: Perform type checking and semantic validation on the resolved `Ast`.
- **Activities**:
    - Verify type compatibility and safety.
    - Analyze and record implicit conversions (e.g., integer promotion, array-to-pointer decay).
    - Determine value categories (LValue/RValue).
    - Populate `SemanticInfo` side tables.
- **Details**: See [semantic_analysis_design.md](file:///home/bungcip/cendol/design-document/semantic_analysis_design.md).

### 3. MIR Generation Phase
- **Entry point**: `MirGen::visit_module`.
- **Goal**: Convert annotated `Ast` with `SemanticInfo` into MIR.
- **Details**: See [mir_design.md](file:///home/bungcip/cendol/design-document/mir_design.md).

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