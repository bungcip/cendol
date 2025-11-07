# Semantic Analysis Phase Design Document

## Overview

The semantic analysis phase processes the flattened AST from the parser and performs comprehensive analysis to ensure the program is semantically correct according to C11 rules. It builds symbol tables, resolves types, checks semantic constraints, and annotates the AST with additional information for code generation.

## Responsibilities

- **Symbol Resolution**: Build and manage symbol tables with scope resolution
- **Type Checking**: Verify type compatibility and constraints
- **Declaration Validation**: Check declaration completeness and validity
- **Constant Evaluation**: Evaluate constant expressions for static assertions and initializers
- **Type Canonicalization**: Ensure consistent type representations
- **Semantic Annotation**: Annotate AST nodes with resolved types and symbols

## Core Data Structures

```rust
/// Main semantic analyzer
pub struct SemanticAnalyzer<'arena, 'src> {
    ast: &'arena mut Ast,
    diag: &'src DiagnosticEngine,

    // Analysis state
    current_scope_id: ScopeId,
    function_scope: Option<ScopeId>,
    loop_nest_depth: u32,
    switch_nest_depth: u32,
}

/// Semantic analysis result
pub struct SemanticOutput {
    pub errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
}
```

### Symbol Table Management

```rust
/// Symbol table using flattened storage
pub struct SymbolTable {
    entries: Vec<SymbolEntry>,
    scopes: Vec<Scope>,
    current_scope_id: ScopeId,
}

/// Individual symbol entry (matches AST design)
pub type SymbolEntry = crate::ast::SymbolEntry;

/// Scope ID for efficient scope references
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = Self(unsafe { NonZeroU32::new_unchecked(1) });

    pub fn new(id: u32) -> Option<Self> {
        NonZeroU32::new(id).map(Self)
    }

    pub fn get(self) -> u32 {
        self.0.get()
    }
}

/// Scope information
#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntryRef>,
    pub kind: ScopeKind,
    pub level: u32,
}

/// Scope types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Global,
    File,
    Function,
    Block,
    FunctionPrototype,
}
```

### Type System

```rust
/// Type table for canonicalization (matches AST design)
pub type TypeTable = crate::ast::Ast; // Types are stored in the same flattened AST

/// Type operations
impl TypeTable {
    pub fn canonicalize_type(&mut self, ty: Type) -> TypeRef {
        // Implementation for type canonicalization
        // Returns existing type if equivalent, creates new one otherwise
        todo!()
    }

    pub fn types_compatible(&self, left: TypeRef, right: TypeRef) -> bool {
        // C11 type compatibility rules
        todo!()
    }
}
```

## Analysis Algorithm

The semantic analyzer performs a multi-pass traversal of the flattened AST:

1. **Symbol Collection Pass**:
   - Traverse AST to collect all declarations
   - Build symbol table with scopes
   - Handle forward declarations and prototypes
   - Detect redeclarations and conflicts

2. **Type Resolution Pass**:
   - Resolve typedef names to underlying types
   - Complete incomplete types (structs, unions, enums)
   - Canonicalize all types for efficient comparison
   - Validate type completeness for definitions

3. **Semantic Validation Pass**:
   - Type check all expressions and assignments
   - Validate function calls and argument compatibility
   - Check control flow constraints (return statements, etc.)
   - Evaluate constant expressions for static assertions
   - Resolve _Generic selections

4. **Annotation Pass**:
   - Annotate AST nodes with resolved types and symbols
   - Mark symbol references and definitions
   - Prepare AST for code generation

## Key Analysis Features

### Symbol Resolution
- **Scope Management**: Hierarchical scope resolution (global → file → function → block)
- **Name Lookup**: Efficient symbol resolution with proper shadowing rules
- **Label Resolution**: Track goto labels and their definitions within function scope
- **Declaration Checking**: Validate declaration syntax and semantics

### Type System
- **Type Equivalence**: C11 type compatibility and equivalence rules
- **Qualifier Propagation**: Handle const/volatile/restrict/_Atomic qualifiers
- **Pointer Types**: Validate pointer arithmetic and conversions
- **Function Types**: Check parameter and return type compatibility
- **Array Types**: Handle VLA and flexible array members

### Constant Evaluation
- **Integer Constants**: Evaluate arithmetic expressions at compile time
- **Static Assertions**: Validate _Static_assert conditions
- **Initializer Constants**: Check constant initializers for static storage
- **Enumeration Values**: Resolve enum constant values

### Error Recovery
- **Continue Analysis**: Attempt to continue analysis after errors
- **Error Propagation**: Track error locations and provide detailed diagnostics
- **Partial Results**: Generate partial results even with semantic errors