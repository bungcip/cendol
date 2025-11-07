# Semantic Analysis Phase Design Document

## Responsibilities
- Symbol table management and scope resolution
- Type checking and type equivalence
- Constant expression evaluation
- Declaration checking and validity
- _Static_assert evaluation
- _Generic selection resolution

## Data Structures

```rust
/// Symbol table entry
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind,
    pub type_info: Option<&'arena Type<'arena>>,
    pub storage_class: Option<StorageClass>,
    pub scope: ScopeId,
    pub definition_location: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
}

/// Symbol kinds
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
        initializer: Option<ConstantExpression>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: Vec<ParameterInfo>,
    },
    Typedef {
        underlying_type: &'arena Type<'arena>,
    },
    EnumConstant {
        value: Option<i64>,
    },
    Label {
        is_defined: bool,
        is_used: bool,
    },
    StructOrUnion {
        is_complete: bool,
        members: Option<Vec<MemberInfo>>,
        size: Option<usize>,
        alignment: Option<usize>,
    },
    Macro {
        definition: MacroDef,
        is_builtin: bool,
    },
}

/// Scope management
pub struct ScopeManager {
    scopes: Vec<Scope>,
    current_scope: ScopeId,
    global_scope: ScopeId,
    // For file scope variables
    translation_unit_scope: ScopeId,
}

/// Scope structure
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntry>,
    pub is_block_scope: bool,
    pub function_scope: Option<FunctionScopeId>,
}

/// Type representation (from AST design)
pub struct Type<'arena> {
    pub kind: TypeKind<'arena>,
    pub qualifiers: TypeQualifiers,
    pub size: Option<usize>,
    pub alignment: Option<usize>,
}
```

## Semantic Analysis Algorithm

1. **First pass**: Collect all declarations and build symbol table
2. **Second pass**: Complete type information and resolve forward references
3. **Third pass**: Check semantics and generate warnings/errors
4. **Fourth pass**: Final validation and optimization preparation

## Type System Features

- **Complete type checking** for C11 standard compliance
- **Atomic types** (_Atomic) with proper synchronization semantics
- **Complex types** (_Complex)
- **Alignment specifiers** (_Alignas)
- **Type qualifiers** (const, volatile, restrict, _Atomic)
- **Pointer arithmetic** validation
- **Function type** checking with parameter and return types
- **Array bounds** checking (flexible array members)