# Semantic Lowering Phase Design

## Overview

The Semantic Lowering phase is the "First Stage" of semantic analysis. It is responsible for bridging the gap between the purely syntactic `ParsedAst` produced by the parser and the enriched, type-resolved `Ast` used by the analyzer and codegen.

## Core Responsibilities

1. **Symbol Registration**: Identify all declarations (variables, functions, typedefs, types) and register them in the `SymbolTable`.
2. **Type Resolution**: Map syntactic type specifiers (e.g., `int`, `struct S`) and declarators (pointers, arrays, functions) to canonical `TypeRef`s in the `TypeRegistry`.
3. **Scope Management**: Construct the hierarchical scope tree (`ScopeId`) and link declarations to their appropriate scopes.
4. **AST Transformation**: Convert generic `ParsedNode`s into specialized semantic `NodeKind` variants (e.g., `VarDecl`, `FunctionDecl`).

## The `LowerCtx`

The lowering process is managed by `LowerCtx` (in `src/semantic/lowering.rs`). It maintains the state of:
- The current scope being processed.
- The symbol table and type registry being populated.
- Maps between `ParsedNodeRef` and resulting `NodeRef`s.

## Lowering Algorithm

### 1. Specifier Processing
C declarations mix storage classes (`static`, `extern`), qualifiers (`const`, `volatile`), and type specifiers. The lowering phase extracts these into a `DeclSpecInfo` structure before processing individual declarators.

### 2. Declarator Application
C's "declaration mimics usage" syntax (e.g., `int (*f[5])(void)`) is handled by recursively applying declarator layers to a base type. The lowering phase traverses the `ParsedDeclarator` chain to build the final `QualType`.

### 3. Symbol Insertion
Once a name and its final type are resolved:
- A new `Symbol` is created.
- The symbol is inserted into the current scope.
- If a redefinition is detected (e.g., duplicate variable name in same block), a semantic error is reported.

### 4. Tag Resolution
Struct, union, and enum tags are tracked in a separate namespace (as required by C). The lowerer handles forward declarations (`struct S;`) and ensures multiple declarations of the same tag resolve to the same underlying type entity.

## Handling C23 Features

- **Enhanced Enums**: Lowering handles the `: underlying_type` syntax and ensures enumerators are checked against this type.
- **`constexpr`**: (Future) Lowering will flag declarations with the `constexpr` storage class for subsequent evaluation.
- **Attributes**: The lowerer processes `[[...]]` attributes (currently limited) to influence symbol properties like linkage or visibility.