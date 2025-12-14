# Semantic Analysis Phase Design Document

## Overview

The semantic analysis phase processes the flattened AST from the parser and performs comprehensive analysis to ensure the program is semantically correct according to C11 rules. It builds symbol tables, resolves identifiers, checks semantic constraints, and annotates the AST with symbol references for later phases.

## Responsibilities

- **Symbol Resolution**: Build and manage symbol tables with hierarchical scope resolution
- **Identifier Resolution**: Resolve identifier references to their declarations
- **Declaration Validation**: Check declaration completeness and detect redeclarations
- **Scope Management**: Maintain hierarchical scopes (global, function, block)
- **Semantic Annotation**: Annotate AST nodes with resolved symbol references

## Core Data Structures

```rust
/// Main semantic analyzer - orchestrates all phases
pub struct SemanticAnalyzer<'arena, 'src> {
    ast: &'arena mut Ast,
    diag: &'src mut DiagnosticEngine,
    pub symbol_table: SymbolTable,
    pub scope_stack: Vec<ScopeId>,
}

/// Semantic analysis result
pub struct SemanticOutput {
    pub diagnostics: Vec<Diagnostic>, // Reuses general diagnostic system
}
```

### Symbol Table Management

```rust
/// Symbol table using flattened storage
#[derive(Debug)]
pub struct SymbolTable {
    pub entries: Vec<SymbolEntry>,
    pub scopes: Vec<Scope>,
    current_scope_id: ScopeId,
    next_scope_id: u32,
}

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

### Symbol Entry Structure

```rust
/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol entries are stored in a separate Vec<SymbolEntry> with SymbolEntryRef references.
#[derive(Debug)]
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind, // e.g., Variable, Function, Typedef
    pub type_info: TypeRef,
    pub storage_class: Option<StorageClass>,
    pub scope_id: u32, // Reference to the scope where it's defined
    pub definition_span: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
}

/// Defines the kind of symbol.
#[derive(Debug)]
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
        // Initializer might be an AST node or a constant value
        initializer: Option<NodeRef>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: Vec<FunctionParameter>,
    },
    Typedef {
        aliased_type: TypeRef,
    },
    EnumConstant {
        value: i64, // Resolved constant value
    },
    Label {
        is_defined: bool,
        is_used: bool,
    },
    Record {
        is_complete: bool,
        members: Vec<StructMember>,
        size: Option<usize>,
        alignment: Option<usize>,
    },
    // Add other symbol kinds as needed (e.g., Macro, BlockScope)
}
```

## Analysis Algorithm

The semantic analyzer performs a four-phase traversal of the flattened AST:

1. **Symbol Collection Pass** (`collect_symbols`):
   - Traverse AST to collect all declarations and function definitions
   - Build hierarchical symbol table with proper scope management
   - Handle function parameters and local variable declarations
   - Detect redeclaration errors within the same scope
   - Create function scopes for each function definition

2. **Name Resolution Pass** (`resolve_names`):
   - Resolve identifier references to their symbol declarations
   - Annotate AST nodes with symbol references using interior mutability
   - Mark symbols as referenced when they are used
   - Report undeclared identifier errors

3. **Type Resolution Pass** (`resolve_types`):
   - Set resolved_type on AST nodes based on symbol information
   - Build canonical type representations for semantic analysis
   - Propagate type information through expressions

4. **Type Checking Pass** (`check_types`):
   - Validate type compatibility in expressions and assignments
   - Check function call argument types against parameter types
   - Detect incompatible pointer operations and conversions
   - Report semantic type errors

## Key Analysis Features

### Symbol Resolution
- **Scope Management**: Hierarchical scope resolution with parent-child relationships
- **Name Lookup**: Efficient symbol resolution from current scope outward
- **Function Scoping**: Each function gets its own scope containing parameters and locals
- **Block Scoping**: Nested compound statements create block scopes
- **Declaration Processing**: Handles both global declarations and function-local declarations

### Identifier Resolution
- **Symbol Lookup**: Searches current scope and parent scopes for symbol declarations
- **Reference Annotation**: Uses `Cell<Option<SymbolEntryRef>>` for interior mutability
- **Undeclared Identifiers**: Reports errors for identifiers that cannot be resolved
- **Symbol Usage Tracking**: Marks symbols as referenced when used

### Declaration Analysis
- **Function Definitions**: Creates function symbols with parameter information
- **Variable Declarations**: Tracks global vs local variables, storage classes
- **Redeclaration Detection**: Prevents multiple declarations of the same name in same scope
- **Scope-Aware Processing**: Maintains current scope context during AST traversal

### Error Recovery
- **Continue Analysis**: Attempts to continue analysis after encountering errors
- **Diagnostic Reporting**: Uses the general diagnostic system for error and warning reporting
- **Partial Results**: Generates partial symbol tables even with semantic errors

## Implementation Details

### Scope Management Implementation

The `SymbolTable` provides sophisticated scope management:

```rust
impl SymbolTable {
    pub fn push_scope(&mut self, kind: ScopeKind) -> ScopeId {
        // Creates new scope with incremented ID
    }

    pub fn push_scope_with_id(&mut self, scope_id: ScopeId, kind: ScopeKind) -> ScopeId {
        // Allows explicit scope ID assignment
    }

    pub fn pop_scope(&mut self) -> Option<ScopeId> {
        // Returns to parent scope
    }

    pub fn lookup_symbol(&self, name: Symbol) -> Option<(SymbolEntryRef, ScopeId)> {
        // Searches current and parent scopes
    }
}
```

### AST Traversal Strategy

The analyzer uses stack-based traversal to process the flattened AST:

- **Depth-First Traversal**: Visits nodes in execution order
- **Scope-Aware Processing**: Maintains current scope context
- **Child Node Discovery**: Uses `get_child_nodes()` to find AST relationships
- **Visited Node Tracking**: Prevents infinite loops with `BitVec` tracking

### Function and Declaration Processing

- **Function Analysis**: Extracts function names, parameters, and creates function scopes
- **Parameter Processing**: Adds function parameters to function scope
- **Local Declaration Handling**: Processes declarations within function bodies
- **For Loop Scoping**: Special handling for variables declared in for loop initialization

## Future Extensions

The current implementation provides a foundation for future enhancements:

- **Type Checking**: Full type compatibility and constraint validation
- **Constant Evaluation**: Compile-time evaluation of constant expressions
- **Control Flow Analysis**: Validation of goto labels and control flow
- **Initialization Checking**: Validation of variable initializers
- **Cross-Reference Analysis**: Advanced usage analysis and optimization hints