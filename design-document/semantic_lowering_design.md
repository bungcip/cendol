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

The semantic lowering phase bridges the gap between the grammar-oriented parser AST and the type-resolved semantic AST (HIR). It handles all C-style declaration forms.

## Core Components

### 1. Lowering Context (`LowerCtx`)

```rust
pub(crate) struct LowerCtx<'a, 'src> {
    pub(crate) parsed_ast: &'a ParsedAst,
    pub(crate) ast: &'a mut Ast,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) symbol_table: &'a mut SymbolTable,
    pub(crate) has_errors: bool,
    pub(crate) registry: &'a mut TypeRegistry,
}
```

### 2. Declaration Specifier Info (`DeclSpecInfo`)

```rust
#[derive(Debug, Clone, Default)]
pub struct DeclSpecInfo {
    pub storage: Option<StorageClass>,
    pub qualifiers: TypeQualifiers,
    pub base_type: Option<TypeRef>,
    pub is_typedef: bool,
    pub is_inline: bool,
    pub is_noreturn: bool,
}
```

### 3. Core Lowering Functions

#### `lower_declaration`

```rust
pub fn lower_declaration(
    ast: &mut Ast,
    decl_node: NodeRef,
    ctx: &mut LowerCtx,
) -> Vec<NodeRef> {
    // 1. Parse and validate declaration specifiers
    // 2. Process each init-declarator into semantic nodes
    // 3. Return vector of semantic nodes
}
```

#### `lower_decl_specifiers`

```rust
fn lower_decl_specifiers(
    specs: &[DeclSpecifier],
    ctx: &mut LowerCtx,
) -> DeclSpecInfo {
    // Process storage classes, type qualifiers, type specifiers
    // Validate combinations and report errors
    // Return consolidated specifier information
}
```

#### `lower_init_declarator`

```rust
fn lower_init_declarator(
    ast: &mut Ast,
    spec: &DeclSpecInfo,
    init: InitDeclarator,
    ctx: &mut LowerCtx,
) -> NodeRef {
    // 1. Resolve final type (base + declarator)
    // 2. Handle typedefs, functions, and variables
    // 3. Create appropriate semantic node
    // 4. Update symbol table
}
```

## Type Resolution and Merging

### Type Specifier Resolution

```rust
fn resolve_type_specifier(
    ts: &TypeSpecifier,
    ctx: &mut LowerCtx,
) -> Result<TypeRef, SemanticError> {
    match ts {
        TypeSpecifier::Void => Ok(Type::new(TypeKind::Void)),
        TypeSpecifier::Char => Ok(Type::new(TypeKind::Char { is_signed: true })),
        TypeSpecifier::Int => Ok(Type::new(TypeKind::Int { is_signed: true })),
        TypeSpecifier::Long => Ok(Type::new(TypeKind::Long { is_signed: true, is_long_long: false })),
        TypeSpecifier::Float => Ok(Type::new(TypeKind::Float)),
        TypeSpecifier::Double => Ok(Type::new(TypeKind::Double { is_long_double: false })),
        TypeSpecifier::Signed => {
            // Merge with existing base type
            // If no base type, default to signed int
        }
        TypeSpecifier::Unsigned => {
            // Merge with existing base type
            // If no base type, default to unsigned int
        }
        TypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            ctx.symbol_table.lookup_symbol(*name)
                .map(|(entry_ref, _)| {
                    let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
                    if let SymbolKind::Typedef { aliased_type } = entry.kind {
                        Ok(aliased_type)
                    } else {
                        Err(SemanticError::IncompleteType { name: *name, location: span })
                    }
                })
                .unwrap_or_else(|| Err(SemanticError::UndeclaredIdentifier { name: *name, location: span }))
        }
        // Handle other type specifiers
    }
}
```

### Type Merging Logic

```rust
fn merge_base_type(
    existing: Option<TypeRef>,
    new_type: TypeRef,
    ctx: &mut LowerCtx,
) -> Option<TypeRef> {
    match existing {
        None => Some(new_type),
        Some(existing_ref) => {
            let existing_type = ctx.ast.get_type(existing_ref);
            let new_type_info = ctx.ast.get_type(new_type);
            
            // Handle signed/unsigned merging
            match (&existing_type.kind, &new_type_info.kind) {
                (TypeKind::Int { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned int overrides signed int
                    Some(new_type)
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    // Keep unsigned
                    Some(existing_ref)
                }
                // Handle long/long long combinations
                (TypeKind::Long { is_long_long: false, .. }, TypeKind::Long { is_long_long: true, .. }) => {
                    // long long overrides long
                    Some(new_type)
                }
                // Handle other combinations
                _ => Some(existing_ref) // Keep existing for now
            }
        }
    }
}
```

## Error Handling

### Semantic Error Types

```rust
pub enum SemanticError {
    DuplicateStorageClass,
    IllegalTypedefStorage,
    MissingBaseType,
    InvalidTypeCombination,
    // ... other error types
}
```

### Error Reporting

```rust
impl LowerCtx {
    pub fn report_error(&mut self, error: SemanticError, location: SourceSpan) {
        self.errors.push(error);
        // Convert to diagnostic
        let diag = match error {
            SemanticError::DuplicateStorageClass => Diagnostic {
                level: DiagnosticLevel::Error,
                message: "Duplicate storage class specifier".to_string(),
                location,
                code: Some("E001".to_string()),
                hints: vec!["Remove duplicate storage class specifier".to_string()],
                related: Vec::new(),
            },
            // Handle other error types
        };
        self.diag.report_diagnostic(diag);
    }
}
```

## Symbol Table Integration

### Symbol Entry Creation

```rust
fn create_symbol_entry(
    name: Symbol,
    ty: TypeRef,
    spec: &DeclSpecInfo,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> SymbolEntry {
    let is_global = ctx.current_scope.get() == 1;
    
    let kind = if ty.is_function() {
        SymbolKind::Function {
            is_definition: false,
            is_inline: spec.is_inline,
            is_variadic: false,
            parameters: Vec::new(),
        }
    } else {
        SymbolKind::Variable {
            is_global,
            is_static: spec.storage == Some(StorageClass::Static),
            is_extern: spec.storage == Some(StorageClass::Extern),
            initializer: None,
        }
    };
    
    SymbolEntry {
        name,
        kind,
        type_info: ty,
        storage_class: spec.storage,
        scope_id: ctx.current_scope.get(),
        definition_span: span,
        is_defined: true,
        is_referenced: false,
        is_completed: true,
    }
}
```

## Implementation Plan

### Phase 1: Core Infrastructure

1. **Create `lower.rs` module** with basic structure
2. **Implement `LowerCtx`** with error collection
3. **Add `DeclSpecInfo` struct** for tracking specifiers
4. **Integrate into semantic analyzer** as a new phase

### Phase 2: Specifier Processing

1. **Implement `lower_decl_specifiers`** function
2. **Add type specifier resolution** for all C types
3. **Implement type merging logic** for complex combinations
4. **Add validation** for illegal specifier combinations

### Phase 3: Declarator Processing

1. **Implement `lower_init_declarator`** function
2. **Add type application** for pointers, arrays, functions
3. **Handle typedef declarations** separately
4. **Create semantic nodes** (VarDecl, FunctionDecl, TypedefDecl)

### Phase 4: Integration and Testing

1. **Integrate with symbol table** for name resolution
2. **Add comprehensive error handling** for all edge cases
3. **Create test cases** for all declaration forms
4. **Validate with existing test suite**

## Key Design Decisions

### 1. Append-Only AST

The lowering phase preserves the original AST structure and creates new semantic nodes, maintaining node stability and avoiding borrow checker conflicts.

### 2. Error Resilience

The lowering continues processing even with partial errors, allowing for better error recovery and reporting multiple issues in a single pass.

### 3. Type Safety

Explicit type resolution with fallback to `Type::Error` for recovery ensures that the semantic AST is always in a valid state.

### 4. Clang/Rustc-Inspired Design

The design mirrors industry-standard HIR construction patterns, making it familiar to compiler developers and easier to extend.

## Extension Points

1. **RecordDecl Support**: Add handling for structs/unions
2. **Function Specifiers**: Implement `inline`, `noreturn` handling
3. **Attribute Handling**: Support for `[[nodiscard]]` and other attributes
4. **Alignment Specifiers**: Add support for `_Alignas`

## Testing Strategy

1. **Unit Tests**: Test individual lowering functions
2. **Integration Tests**: Test full declaration lowering
3. **Regression Tests**: Ensure existing functionality is preserved
4. **Error Case Tests**: Validate error handling and reporting

## Performance Considerations

1. **Minimize AST Traversal**: Process declarations in a single pass
2. **Efficient Type Merging**: Use type interning for common types
3. **Lazy Evaluation**: Defer complex type resolution when possible
4. **Memory Efficiency**: Reuse existing AST infrastructure

This design provides a solid foundation for implementing a robust semantic lowering phase that integrates seamlessly with the existing semantic analysis pipeline while providing the necessary infrastructure for type resolution and code generation.