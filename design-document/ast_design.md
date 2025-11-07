# C11 Compiler AST Design Document - Cache-Friendly & Efficient

## 1. Overview

This document outlines the design for a highly optimized Abstract Syntax Tree (AST) for a new C11 compiler written in Rust. The primary goals for this AST design are:

- **Extreme Performance**: Minimize CPU cycles spent on memory management, indirection, and cache misses.
- **Cache-Friendliness**: Data layout must prioritize spatial locality to minimize CPU cache misses during traversal.
- **Minimal Memory Footprint**: Reduce overall memory usage through compact data structures and efficient storage.
- **C11 Compliance**: Accurately represent all C11 language constructs.
- **Flexibility**: Allow for easy annotation during semantic analysis and transformation during optimization phases.

## 2. Core Principles for Efficiency

To achieve the design goals, the AST will adhere to the following core principles:

1.  **Arena Allocation**: All AST nodes will be allocated within a single, contiguous memory region (an arena). This ensures excellent spatial locality, reducing cache misses during tree traversal.
2.  **Symbol Interning**: All identifiers, string literals, and other frequently repeated strings will be "interned" into a global symbol table, represented by compact integer IDs (`Symbol`). This drastically reduces memory usage and enables `O(1)` string comparisons.
3.  **Compressed Source Locations**: Source file and offset information will be packed into a single `u32` or `u64` to minimize the size of `SourceSpan` within each AST node.
4.  **Hot/Cold Data Splitting**: Frequently accessed data (e.g., `NodeKind`, `SourceSpan`) will be kept directly within the `Node` struct, while less frequently accessed or larger data (e.g., lists of parameters, complex initializers) will be stored separately and referenced via arena-allocated slices or pointers.
5.  **Struct-of-Arrays (SoA) for Collections**: For collections of similar items (e.g., function parameters, struct members), a SoA approach might be considered where appropriate to improve cache utilization over Array-of-Structs (AoS).
6.  **Minimal Indirection**: Avoid excessive use of `Box`, `Rc`, `Arc`, or deep pointer chains. References (`&'arena T`) will be preferred.
7.  **Inline Storage for Simple Types**: Primitive types and small enums will be stored directly within AST nodes.

## 3. Fundamental Data Structures

### 3.1. Symbol Interning

All unique strings (identifiers, string literals, etc.) are interned.

```rust
use std::num::NonZeroU32;
use hashbrown::HashMap;

/// Represents an interned string.
/// Uses NonZeroU32 for compact Option<Symbol> (0 is reserved for None).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(NonZeroU32);

/// The string interner.
pub struct StringInterner {
    map: HashMap<String, Symbol>,
    strings: Vec<String>, // Stores the actual strings, indexed by Symbol.0 - 1
    next_id: u32,
}

impl StringInterner {
    pub fn new() -> Self {
        StringInterner {
            map: HashMap::new(),
            strings: Vec::new(),
            next_id: 1, // Start from 1 for NonZeroU32
        }
    }

    pub fn get_or_intern(&mut self, s: &str) -> Symbol {
        if let Some(&symbol) = self.map.get(s) {
            return symbol;
        }

        let id = self.next_id;
        self.next_id += 1;
        let symbol = Symbol(NonZeroU32::new(id).expect("Symbol ID overflow"));

        self.map.insert(s.to_string(), symbol);
        self.strings.push(s.to_string()); // Store a copy
        symbol
    }

    pub fn resolve(&self, symbol: Symbol) -> &str {
        &self.strings[(symbol.0.get() - 1) as usize]
    }
}
```

**Benefits:**
-   **Deduplication**: Only one copy of each unique string is stored.
-   **Cache-Friendly AST**: AST nodes only store a `Symbol` (4 bytes), dramatically reducing the size of identifier nodes.
-   **Fast Comparisons**: `O(1)` integer comparison for symbol equality.
-   **Compact Option**: `NonZeroU32` allows `Option<Symbol>` to be the same size as `Symbol`.

### 3.2. Source Location Tracking

Efficiently stores file ID and byte offset.

```rust
/// Identifies a specific source file/module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceId(NonZeroU32);

/// Represents a packed file ID and byte offset in a single u32.
/// Designed to be 4 bytes.
/// - Bits 0-21: Byte Offset (max 4 MiB file size)
/// - Bits 22-31: Source ID Index (max 1023 unique source files)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceLoc(u32);

impl SourceLoc {
    const OFFSET_MASK: u32 = (1 << 22) - 1; // 22 bits for offset
    const ID_SHIFT: u32 = 22; // Shift for SourceId

    pub fn new(source_id: SourceId, offset: u32) -> Self {
        assert!(offset <= Self::OFFSET_MASK, "Offset exceeds 4 MiB limit");
        assert!(source_id.0.get() <= (1 << (32 - Self::ID_SHIFT)) - 1, "SourceId exceeds 1023 limit");
        
        let packed = (offset & Self::OFFSET_MASK) | (source_id.0.get() << Self::ID_SHIFT);
        SourceLoc(packed)
    }

    pub fn source_id(&self) -> SourceId {
        SourceId(NonZeroU32::new((self.0 >> Self::ID_SHIFT) & ((1 << (32 - Self::ID_SHIFT)) - 1)).expect("Invalid SourceId"))
    }

    pub fn offset(&self) -> u32 {
        self.0 & Self::OFFSET_MASK
    }
}

/// Represents a range in the source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    pub start: SourceLoc,
    pub end: SourceLoc,
}
```

**Rationale for SourceLoc Packing:**
-   **Compactness**: `SourceLoc` is 4 bytes, `SourceSpan` is 8 bytes.
-   **Sufficient Capacity**: 1023 files and 4 MiB per file are ample for most C projects. Larger files/projects would require `u64` for `SourceLoc`.

### 3.3. Arena Allocation

The `bumpalo` crate is an excellent choice for arena allocation in Rust.

```rust
use bumpalo::Bump;

/// The arena for allocating AST nodes.
pub type Arena = Bump;
```

**Benefits:**
-   **Performance**: Extremely fast allocation (just a pointer bump).
-   **Cache Locality**: Nodes are allocated contiguously, improving cache hit rates during traversal.
-   **No Deallocation Overhead**: The entire arena is freed at once, avoiding per-node deallocation costs.

### 3.4. Node and NodeKind (Cache-Optimized)

The primary AST node structure is built for minimal size and indirection. It uses separate structs for complex statements (e.g., `IfStmt`, `ForStmt`) to keep the main `NodeKind` enum small and cache-friendly.

```rust
use std::cell::Cell; // For interior mutability (e.g., type annotation)

/// The primary AST node structure.
/// It is allocated in the arena and is a reference in most contexts.
/// Designed to be small and cache-friendly.
#[derive(Debug)]
pub struct Node<'arena> {
    pub kind: NodeKind<'arena>,
    pub span: SourceSpan,
    // Uses Cell for Interior Mutability: allows type checking to annotate the AST
    // without requiring mutable access to the entire tree structure.
    pub resolved_type: Cell<Option<&'arena Type<'arena>>>, // Hot data
    // After semantic analysis, for Ident nodes, this will point to the resolved symbol entry.
    pub resolved_symbol: Cell<Option<&'arena SymbolEntry<'arena>>>, // Hot data
}

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
#[derive(Debug)]
pub struct SymbolEntry<'arena> {
    pub name: Symbol,
    pub kind: SymbolKind<'arena>, // e.g., Variable, Function, Typedef
    pub type_info: &'arena Type<'arena>,
    pub storage_class: Option<StorageClass>,
    pub scope_id: u32, // Reference to the scope where it's defined
    pub definition_span: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
    // Add other relevant symbol information here (e.g., value for constants, linkage)
}

/// Defines the kind of symbol.
#[derive(Debug)]
pub enum SymbolKind<'arena> {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
        // Initializer might be an AST node or a constant value
        initializer: Option<&'arena Node<'arena>>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: &'arena [FunctionParameter<'arena>],
    },
    Typedef {
        aliased_type: &'arena Type<'arena>,
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
        members: &'arena [StructMember<'arena>],
        size: Option<usize>,
        alignment: Option<usize>,
    },
    // Add other symbol kinds as needed (e.g., Macro, BlockScope)
}

/// The core enum defining all possible AST node types for C11.
/// Variants are kept small; larger data is referenced via arena-allocated structs.
#[derive(Debug)]
pub enum NodeKind<'arena> {
    // --- Literals (Inline storage for common types) ---
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(Symbol),
    LiteralChar(char),

    // --- Expressions ---
    // Ident now includes a Cell for resolved SymbolEntry after semantic analysis
    Ident(Symbol, Cell<Option<&'arena SymbolEntry<'arena>>>),
    UnaryOp(UnaryOp, &'arena Node<'arena>),
    BinaryOp(BinaryOp, &'arena Node<'arena>, &'arena Node<'arena>),
    TernaryOp(&'arena Node<'arena>, &'arena Node<'arena>, &'arena Node<'arena>),

    PostIncrement(&'arena Node<'arena>),
    PostDecrement(&'arena Node<'arena>),

    Assignment(BinaryOp, &'arena Node<'arena> /* lhs */, &'arena Node<'arena> /* rhs */),
    FunctionCall(&'arena Node<'arena> /* func */, &'arena [&'arena Node<'arena>] /* args */),
    MemberAccess(&'arena Node<'arena> /* object */, Symbol /* field */, bool /* is_arrow */),
    IndexAccess(&'arena Node<'arena> /* array */, &'arena Node<'arena> /* index */),

    Cast(&'arena Type<'arena>, &'arena Node<'arena>),
    SizeOfExpr(&'arena Node<'arena>),
    SizeOfType(&'arena Type<'arena>),
    AlignOf(&'arena Type<'arena>), // C11 _Alignof

    CompoundLiteral(&'arena Type<'arena>, &'arena Initializer<'arena>),
    GenericSelection(&'arena Node<'arena> /* controlling_expr */, &'arena [GenericAssociation<'arena>]), // C11 _Generic
    VaArg(&'arena Node<'arena> /* va_list_expr */, &'arena Type<'arena>), // va_arg macro expansion

    // --- Statements (Complex statements are separate structs) ---
    CompoundStatement(&'arena [Node<'arena>] /* block items */),
    If(&'arena IfStmt<'arena>),
    While(&'arena WhileStmt<'arena>),
    DoWhile(&'arena Node<'arena> /* body */, &'arena Node<'arena> /* condition */),
    For(&'arena ForStmt<'arena>),

    Return(Option<&'arena Node<'arena>>),
    Break,
    Continue,
    Goto(Symbol),
    Label(Symbol, &'arena Node<'arena> /* statement */),

    Switch(&'arena Node<'arena> /* condition */, &'arena Node<'arena> /* body statement */),
    Case(&'arena Node<'arena> /* const_expr */, &'arena Node<'arena> /* statement */),
    CaseRange(&'arena Node<'arena> /* start_expr */, &'arena Node<'arena> /* end_expr */, &'arena Node<'arena> /* statement */), // GNU Extension often supported
    Default(&'arena Node<'arena> /* statement */),

    EmptyStatement, // ';'

    // --- Declarations & Definitions ---
    Declaration(&'arena DeclarationData<'arena>),
    FunctionDef(&'arena FunctionDefData<'arena>),
    EnumConstant(Symbol, Option<&'arena Node<'arena>> /* value expr */),
    StaticAssert(&'arena Node<'arena> /* condition */, Symbol /* message */),

    // --- Top Level ---
    TranslationUnit(&'arena [Node<'arena>] /* top-level declarations */),
}

// Structs for Large/Indirect Variants (to keep NodeKind size small and cache-friendly)
// These are allocated in the arena and referenced by NodeKind.

#[derive(Debug)]
pub struct IfStmt<'arena> {
    pub condition: &'arena Node<'arena>,
    pub then_branch: &'arena Node<'arena>,
    pub else_branch: Option<&'arena Node<'arena>>,
}

#[derive(Debug)]
pub struct WhileStmt<'arena> {
    pub condition: &'arena Node<'arena>,
    pub body: &'arena Node<'arena>,
}

#[derive(Debug)]
pub struct ForStmt<'arena> {
    pub init: Option<&'arena Node<'arena>>, // Can be Declaration or Expression
    pub condition: Option<&'arena Node<'arena>>,
    pub increment: Option<&'arena Node<'arena>>,
    pub body: &'arena Node<'arena>,
}

#[derive(Debug)]
pub struct DeclarationData<'arena> {
    pub specifiers: &'arena [DeclSpecifier<'arena>],
    pub init_declarators: &'arena [InitDeclarator<'arena>],
}

#[derive(Debug)]
pub struct InitDeclarator<'arena> {
    pub declarator: &'arena Declarator<'arena>,
    pub initializer: Option<&'arena Initializer<'arena>>,
}

#[derive(Debug)]
pub struct FunctionDefData<'arena> {
    pub specifiers: &'arena [DeclSpecifier<'arena>],
    pub declarator: &'arena Declarator<'arena>,
    pub body: &'arena Node<'arena>, // A CompoundStatement
}

#[derive(Debug)]
pub struct ParamData<'arena> {
    pub specifiers: &'arena [DeclSpecifier<'arena>],
    pub declarator: Option<&'arena Declarator<'arena>>, // Optional name for abstract declarator
}

#[derive(Debug)]
pub struct RecordDefData<'arena> {
    pub tag: Option<Symbol>, // None if anonymous
    pub members: Option<&'arena [DeclarationData<'arena>]>, // Field declarations
    pub is_union: bool,
}

#[derive(Debug)]
pub struct EnumDefData<'arena> {
    pub tag: Option<Symbol>,
    pub enumerators: Option<&'arena [Node<'arena>]>, // List of EnumConstant nodes
}

// Declaration Specifiers combine StorageClass, TypeQualifiers, and TypeSpecifiers
#[derive(Debug)]
pub struct DeclSpecifier<'arena> {
    pub storage_class: Option<StorageClass>,
    pub type_specifier: TypeSpecifier<'arena>,
}

// Type Specifiers (C11)
#[derive(Debug)]
pub enum TypeSpecifier<'arena> {
    Void, Char, Short, Int, Long, Float, Double, Signed, Unsigned,
    Bool, Complex, Atomic(&'arena Type<'arena>), // _Bool, _Complex, _Atomic
    Record(bool /* is_union */, Option<Symbol> /* tag */, Option<&'arena RecordDefData<'arena>> /* definition */),
    Enum(Option<Symbol> /* tag */, Option<&'arena [Node<'arena>]> /* enumerators */),
    TypedefName(Symbol),
}

// Storage Class Specifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageClass {
    Typedef, Extern, Static, Auto, Register, ThreadLocal, // C11 _Thread_local
}

// Type Qualifiers (bitflags for compactness)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeQualifiers(u8); // Using u8 for bitflags

impl TypeQualifiers {
    pub const CONST: Self = Self(1 << 0);
    pub const VOLATILE: Self = Self(1 << 1);
    pub const RESTRICT: Self = Self(1 << 2);
    pub const ATOMIC: Self = Self(1 << 3); // C11 _Atomic
    // Add methods for checking/setting flags
}

// Unary Operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Plus, Minus, Deref, AddrOf, BitNot, LogicNot,
    PreIncrement, PreDecrement,
}

// Binary Operators (includes assignment types)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add, Sub, Mul, Div, Mod,
    BitAnd, BitOr, BitXor, LShift, RShift,
    Equal, NotEqual, Less, LessEqual, Greater, GreaterEqual,
    LogicAnd, LogicOr,
    Comma,
    Assign, AssignAdd, AssignSub, AssignMul, AssignDiv, AssignMod,
    AssignBitAnd, AssignBitOr, AssignBitXor, AssignLShift, AssignRShift,
}

// C11 _Generic Association
#[derive(Debug)]
pub struct GenericAssociation<'arena> {
    pub type_name: Option<&'arena Type<'arena>>, // None for 'default:'
    pub result_expr: &'arena Node<'arena>,
}

// Complex part of C declaration: the part that applies pointers, arrays, and functions
// This recursive structure allows for declarations like `int (*(*fp)())[10];`
#[derive(Debug)]
pub enum Declarator<'arena> {
    Identifier(Symbol, TypeQualifiers, Option<&'arena Declarator<'arena>>), // Base case: name (e.g., `x`)
    Pointer(TypeQualifiers, Option<&'arena Declarator<'arena>>), // e.g., `*`
    Array(&'arena Declarator<'arena>, &'arena ArraySize<'arena>), // e.g., `[10]`
    Function(&'arena Declarator<'arena>, &'arena [ParamData<'arena>] /* parameters */), // e.g., `(int x)`
}

// Defines array size (e.g., [10], [*], or [] for flexible array members)
#[derive(Debug)]
pub enum ArraySize<'arena> {
    Expression(&'arena Node<'arena>),
    Star,       // [*] VLA
    Incomplete, // []
    VlaSpecifier(Option<&'arena Node<'arena>> /* VLA size expr */), // `static` or `*` for VLA (C99)
}

// Initializer structure for variables (e.g., int x = 5; or struct s = {1, 2};)
#[derive(Debug)]
pub enum Initializer<'arena> {
    Expression(&'arena Node<'arena>), // = 5
    List(&'arena [DesignatedInitializer<'arena>]), // = { .x = 1, [0] = 2 }
}

// Designated initializer for array/struct lists (C99/C11)
#[derive(Debug)]
pub struct DesignatedInitializer<'arena> {
    pub designation: &'arena [Designator<'arena>],
    pub initializer: &'arena Initializer<'arena>,
}

// A single designator in a list (.field or [index])
#[derive(Debug)]
pub enum Designator<'arena> {
    FieldName(Symbol),
    ArrayIndex(&'arena Node<'arena>), // Index expression
}

// Type representation (for semantic analysis)
// This is a canonical type, distinct from TypeSpecifier which is a syntax construct.
#[derive(Debug)]
pub struct Type<'arena> {
    pub kind: TypeKind<'arena>,
    pub qualifiers: TypeQualifiers,
    pub size: Option<usize>, // Computed during semantic analysis
    pub alignment: Option<usize>, // Computed during semantic analysis
}

#[derive(Debug)]
pub enum TypeKind<'arena> {
    Void,
    Bool,
    Char { is_signed: bool },
    Short { is_signed: bool },
    Int { is_signed: bool },
    Long { is_signed: bool, is_long_long: bool },
    Float,
    Double { is_long_double: bool },
    Complex { base_type: &'arena Type<'arena> }, // C11 _Complex
    Atomic { base_type: &'arena Type<'arena> }, // C11 _Atomic
    Pointer { pointee: &'arena Type<'arena> },
    Array { element_type: &'arena Type<'arena>, size: ArraySizeType<'arena> },
    Function {
        return_type: &'arena Type<'arena>,
        parameters: &'arena [FunctionParameter<'arena>],
        is_variadic: bool,
    },
    Record { // Represents both struct and union
        tag: Option<Symbol>,
        members: &'arena [StructMember<'arena>],
        is_complete: bool,
        is_union: bool, // Differentiate between struct and union
    },
    Enum {
        tag: Option<Symbol>,
        base_type: &'arena Type<'arena>, // Underlying integer type
        enumerators: &'arena [EnumConstant<'arena>],
        is_complete: bool,
    },
    Typedef {
        name: Symbol,
        aliased_type: &'arena Type<'arena>,
    },
    // Placeholder for incomplete types during semantic analysis
    Incomplete,
    Error, // For error recovery
}

#[derive(Debug)]
pub enum ArraySizeType<'arena> {
    Constant(usize),
    Variable(&'arena Node<'arena>), // VLA
    Incomplete,
    Star, // [*] for function parameters
}

#[derive(Debug)]
pub struct FunctionParameter<'arena> {
    pub param_type: &'arena Type<'arena>,
    pub name: Option<Symbol>,
}

#[derive(Debug)]
pub struct StructMember<'arena> {
    pub name: Symbol,
    pub member_type: &'arena Type<'arena>,
    pub bit_field_size: Option<usize>,
    pub location: SourceSpan,
}

#[derive(Debug)]
pub struct EnumConstant<'arena> {
    pub name: Symbol,
    pub value: i64, // Resolved value
    pub location: SourceSpan,
}
```

## 4. Cache-Friendly Traversal and Operations

-   **Iterators**: Provide custom iterators that leverage the arena's contiguous memory for faster traversal.
-   **Visitor Pattern**: Implement a visitor pattern for AST traversal (e.g., for semantic analysis, code generation) that can be optimized for cache access.
-   **Data-Oriented Design (DOD)**: Where possible, consider separating data into flat arrays for specific passes (e.g., a pass that only needs `NodeKind` and `SourceSpan` could iterate over arrays of these, rather than full `Node` structs).

## 5. Future Optimizations

-   **Memory Prefetching**: Explicitly use `core::arch::x86_64::_mm_prefetch` or similar intrinsics for critical traversal paths.
-   **SIMD for Batch Operations**: If applicable, use SIMD instructions for batch processing of AST nodes (e.g., during certain analysis passes).
-   **Custom Allocators**: Explore custom arena allocators that are even more specialized for AST node sizes.

This AST design prioritizes performance and cache efficiency, providing a robust and fast foundation for the C11 compiler.