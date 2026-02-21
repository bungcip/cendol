# Semantic Lowering Phase Design

## Overview

This document outlines the design for implementing a robust semantic lowering phase that transforms parser AST declarations into type-resolved, codegen-ready semantic nodes. The lowering phase will be integrated into the existing semantic analysis pipeline.

## Current Architecture Analysis

The current semantic analysis consists of four phases:

1. **Symbol Collection**: Collects symbols and builds the symbol table
2. **Name Resolution**: Resolves identifiers to symbol table entries
3. **Type Resolution**: Sets resolved types on AST nodes
4. **Type Checking**: Validates type compatibility and safety

## Architecture

The semantic lowering phase bridges the gap between the syntactic `ParsedAst` and the semantic `Ast`. It processes declarations, handles scope management, and populates the symbol table and type registry.

## Core Components

### 1. Lowering Context (`LowerCtx`)

```rust
pub(crate) struct LowerCtx<'a, 'src> {
    pub(crate) parsed_ast: &'a ParsedAst,
    pub(crate) ast: &'a mut Ast,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) symbol_table: &'a mut SymbolTable,
    pub(crate) registry: &'a mut TypeRegistry,
    pub(crate) has_errors: bool,
    // ...
}
```

### 2. Declaration Specifier Info (`DeclSpecInfo`)

Consolidates storage classes, type qualifiers, and base types from a list of `ParsedDeclSpecifier` nodes.

### 3. Core Logic

- **`visit_ast`**: The entry point. Iterates through the `TranslationUnit` children and lowers each one.
- **`lower_declaration`**: Processes `ParsedNodeKind::Declaration`. It handles one or more `ParsedInitDeclarator` items sharing the same specifiers.
- **`lower_function_def`**: Processes `ParsedNodeKind::FunctionDef`, creating a semantic `Function` node and lowering its body.
- **`apply_parsed_declarator`**: Recursively transforms a base `QualType` based on pointer, array, or function declarators.

## Type Resolution

1. **Base Type Resolution**: `convert_parsed_base_type_to_qual_type` maps syntactic type specifiers (like `int`, `struct S`, `typedef_name`) to a canonical `QualType`.
2. **Declarator Application**: `apply_parsed_declarator` adds layers (pointers, arrays, function types) to the base type.
3. **Type Registry**: All unique types are interned in the `TypeRegistry`.

## Symbol Table Integration

Lowering creates symbol entries for all declared names:
- **Variables**: `VarDecl` nodes.
- **Functions**: `FunctionDecl` or `Function` nodes.
- **Typedefs**: `TypedefDecl` nodes.
- **Tags**: Struct, union, and enum tags are tracked for forward declarations and completion.

## Scope Management

Hierarchical scopes are constructed during lowering:
- **File Scope**: Global declarations.
- **Function Scope**: Parameters and labels.
- **Block Scope**: Local variables.
- **Prototype Scope**: Parameters in function declarations.

This design provides a solid foundation for implementing a robust semantic lowering phase that integrates seamlessly with the existing semantic analysis pipeline while providing the necessary infrastructure for type resolution and code generation.