# C11 Compiler AST Design Document - Flattened & Cache-Friendly

## 1. Overview

This document outlines the design for a highly optimized Abstract Syntax Tree (AST) for a new C11 compiler written in Rust. The AST uses a flattened storage approach inspired by https://www.cs.cornell.edu/~asampson/blog/flattening.html, where all nodes are stored in a contiguous array with index-based references. The primary goals for this AST design are:

- **Extreme Performance**: Minimize CPU cycles spent on memory management, indirection, and cache misses through flattened, contiguous storage.
- **Cache-Friendliness**: Data layout prioritizes spatial locality with all nodes in a single contiguous array, minimizing CPU cache misses during traversal.
- **Minimal Memory Footprint**: Reduce overall memory usage through compact data structures, efficient storage, and elimination of pointer overhead.
- **C11 Compliance**: Accurately represent all C11 language constructs.
- **Flexibility**: Allow for easy annotation during semantic analysis and transformation during optimization phases, leveraging index-based access.

## 2. Core Principles for Efficiency

To achieve the design goals, the AST will adhere to the following core principles:

1.  **Flattened Storage**: All AST nodes are stored in a single `Vec<Node>`, providing contiguous memory layout and eliminating pointer indirection for superior cache performance.
2.  **Index-Based References**: Child nodes and related data structures are referenced by `u32` indices into their respective storage vectors, enabling fast, predictable access patterns.
3.  **Symbol Interning**: All identifiers, string literals, and other frequently repeated strings will be "interned" into a global symbol table, represented by compact integer IDs (`Symbol`). This drastically reduces memory usage and enables `O(1)` string comparisons.
4.  **Compressed Source Locations**: Source file and offset information will be packed into a single `u32` or `u64` to minimize the size of `SourceSpan` within each AST node.
5.  **Hot/Cold Data Splitting**: Frequently accessed data (e.g., `NodeKind`, `SourceSpan`) will be kept directly within the `Node` struct, while less frequently accessed or larger data (e.g., lists of parameters, complex initializers) will be stored separately and referenced via indices.
6.  **Struct-of-Arrays (SoA) for Collections**: For collections of similar items (e.g., function parameters, struct members), a SoA approach might be considered where appropriate to improve cache utilization over Array-of-Structs (AoS).
7.  **Minimal Indirection**: Avoid excessive use of `Box`, `Rc`, `Arc`, or deep pointer chains. Index-based access is preferred over references.
8.  **Inline Storage for Simple Types**: Primitive types and small enums will be stored directly within AST nodes.

## 3. Fundamental Data Structures

To achieve flattening, the AST will be stored in a single `Vec<Node>`, with all nodes allocated contiguously. Child nodes are referenced by their index (`u32`) in this vector, eliminating pointer indirection and improving cache locality. This approach allows for better vectorization during traversal and reduces memory fragmentation compared to arena allocation.

### 3.1. Symbol Interning

All unique strings (identifiers, string literals, etc.) are interned using the `symbol_table` crate with global symbol table feature.

```rust
/// Represents an interned string using symbol_table crate.
/// Alias for GlobalSymbol from symbol_table crate with global feature.
pub type Symbol = symbol_table::GlobalSymbol;
```

**Benefits:**
-   **Deduplication**: Only one copy of each unique string is stored globally.
-   **Cache-Friendly AST**: AST nodes only store a `Symbol` (4 bytes), dramatically reducing the size of identifier nodes.
-   **Fast Comparisons**: `O(1)` integer comparison for symbol equality.
-   **Compact Option**: `NonZeroU32` allows `Option<Symbol>` to be the same size as `Symbol`.
-   **Global Interning**: Uses thread-safe global symbol table for efficient interning across the compiler.

### 3.2. Source Location Tracking

Efficiently stores file ID and byte offset, imported from the source_manager module.

```rust
pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};
```

**Rationale for SourceLoc Packing:**
-   **Compactness**: `SourceLoc` is 4 bytes, `SourceSpan` is 8 bytes.
-   **Sufficient Capacity**: 1023 files and 4 MiB per file are ample for most C projects. Larger files/projects would require `u64` for `SourceLoc`.

### 3.3. Flattened AST Storage

Instead of arena allocation, the AST is stored in a single `Vec<Node>`, providing contiguous memory layout.

```rust
/// The flattened AST storage.
/// Contains all AST nodes, types, symbol entries, and initializers in contiguous vectors.
pub struct Ast {
    pub nodes: Vec<Node>,
    pub types: Vec<Type>,
    pub symbol_entries: Vec<SymbolEntry>,
    pub initializers: Vec<Initializer>,
    pub root: Option<NodeRef>,
}

/// Node reference type for referencing child nodes.
pub type NodeRef = NonZeroU32;
pub type TypeRef = NonZeroU32;
pub type SymbolEntryRef = NonZeroU32;
pub type InitializerRef = NonZeroU32;

/// Helper methods for Ast.
impl Ast {
    /// Create a new empty AST
    pub fn new() -> Self {
        Ast {
            nodes: Vec::new(),
            types: Vec::new(),
            symbol_entries: Vec::new(),
            initializers: Vec::new(),
            root: None,
        }
    }

    /// Get the root node of the AST
    pub fn get_root_node(&self) -> Option<&Node> {
        self.root.map(|node_ref| self.get_node(node_ref))
    }

    /// Set the root node of the AST
    pub fn set_root_node(&mut self, node_ref: NodeRef) {
        self.root = Some(node_ref);
    }

    /// Add a node to the AST and return its reference
    pub fn push_node(&mut self, node: Node) -> NodeRef {
        let index = self.nodes.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.nodes.push(node);
        NodeRef::new(index).expect("NodeRef overflow")
    }

    /// Get a node by its reference
    pub fn get_node(&self, index: NodeRef) -> &Node {
        &self.nodes[(index.get() - 1) as usize]
    }

    /// Add a type to the AST and return its reference
    pub fn push_type(&mut self, ty: Type) -> TypeRef {
        let index = self.types.len() as u32 + 1;
        self.types.push(ty);
        TypeRef::new(index).expect("TypeRef overflow")
    }

    /// Get a type by its reference
    pub fn get_type(&self, index: TypeRef) -> &Type {
        let idx = (index.get() - 1) as usize;
        if idx >= self.types.len() {
            panic!(
                "Type index {} out of bounds: types vector has {} elements",
                index.get(),
                self.types.len()
            );
        }
        &self.types[idx]
    }

    /// Add a symbol entry to the AST and return its reference
    pub fn push_symbol_entry(&mut self, entry: SymbolEntry) -> SymbolEntryRef {
        let index = self.symbol_entries.len() as u32 + 1;
        self.symbol_entries.push(entry);
        SymbolEntryRef::new(index).expect("SymbolEntryRef overflow")
    }

    /// Get a symbol entry by its reference
    pub fn get_symbol_entry(&self, index: SymbolEntryRef) -> &SymbolEntry {
        &self.symbol_entries[(index.get() - 1) as usize]
    }

    /// Add an initializer to the AST and return its reference
    pub fn push_initializer(&mut self, init: Initializer) -> InitializerRef {
        let index = self.initializers.len() as u32 + 1;
        self.initializers.push(init);
        InitializerRef::new(index).expect("InitializerRef overflow")
    }

    /// Get an initializer by its reference
    pub fn get_initializer(&self, index: InitializerRef) -> &Initializer {
        &self.initializers[(index.get() - 1) as usize]
    }
}
```

**Benefits:**
-   **Superior Cache Locality**: All nodes are in a single contiguous array, minimizing cache misses.
-   **Index-Based References**: Children are referenced by `u32` indices, eliminating pointer overhead.
-   **Vectorization-Friendly**: Contiguous layout enables SIMD operations during traversal.
-   **Simplified Memory Management**: Single vector allocation/deallocation.

### 3.4. Node and NodeKind (Flattened and Cache-Optimized)

The primary AST node structure is designed for the flattened storage. All references to child nodes use `NodeRef` instead of arena references, enabling contiguous memory layout and index-based access.

```rust
use std::cell::Cell; // For interior mutability (e.g., type annotation)

/// The primary AST node structure.
/// Stored in the flattened Vec<Node>, with index-based references.
/// Designed to be small and cache-friendly.
#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub span: SourceSpan,
    // Uses Cell for Interior Mutability: allows type checking to annotate the AST
    // without requiring mutable access to the entire tree structure.
    pub resolved_type: Cell<Option<TypeRef>>, // Hot data, now ref-based
    // After semantic analysis, for Ident nodes, this will point to the resolved symbol entry.
    pub resolved_symbol: Cell<Option<SymbolEntryRef>>, // Hot data, now ref-based
}

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
    // Add other relevant symbol information here (e.g., value for constants, linkage)
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

/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
/// Maintained original structure for compatibility, but moved to this module.
#[derive(Debug, Clone, Serialize)]
pub enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    LiteralInt(i64), // Parsed integer literal value
    LiteralFloat(f64),
    LiteralString(Symbol),
    LiteralChar(u8),

    // --- Expressions ---
    // Ident now includes a Cell for resolved SymbolEntry after semantic analysis
    Ident(Symbol, Cell<Option<SymbolEntryRef>>),
    UnaryOp(UnaryOp, NodeRef),
    BinaryOp(BinaryOp, NodeRef, NodeRef),
    TernaryOp(NodeRef, NodeRef, NodeRef),
    GnuStatementExpression(NodeRef /* compound statement */, NodeRef /* result expression */),

    PostIncrement(NodeRef),
    PostDecrement(NodeRef),

    Assignment(BinaryOp, NodeRef /* lhs */, NodeRef /* rhs */),
    FunctionCall(NodeRef /* func */, Vec<NodeRef> /* args */),
    MemberAccess(
        NodeRef, /* object */
        Symbol,  /* field */
        bool,    /* is_arrow */
    ),
    IndexAccess(NodeRef /* array */, NodeRef /* index */),

    Cast(TypeRef, NodeRef),
    SizeOfExpr(NodeRef),
    SizeOfType(TypeRef),
    AlignOf(TypeRef), // C11 _Alignof

    CompoundLiteral(TypeRef, InitializerRef),
    GenericSelection(NodeRef /* controlling_expr */, Vec<GenericAssociation>),
    VaArg(NodeRef /* va_list_expr */, TypeRef), // va_arg macro expansion

    // --- Statements (Complex statements are separate structs) ---
    CompoundStatement(Vec<NodeRef> /* block items */),
    If(IfStmt),
    While(WhileStmt),
    DoWhile(NodeRef /* body */, NodeRef /* condition */),
    For(ForStmt),

    Return(Option<NodeRef>),
    Break,
    Continue,
    Goto(Symbol),
    Label(Symbol, NodeRef /* statement */),

    Switch(NodeRef /* condition */, NodeRef /* body statement */),
    Case(NodeRef /* const_expr */, NodeRef /* statement */),
    CaseRange(
        NodeRef, /* start_expr */
        NodeRef, /* end_expr */
        NodeRef, /* statement */
    ), // GNU Extension often supported
    Default(NodeRef /* statement */),

    ExpressionStatement(Option<NodeRef> /* expression */), // Expression followed by ';'
    EmptyStatement,                                        // ';'

    // --- Declarations & Definitions ---
    Declaration(DeclarationData),
    FunctionDef(FunctionDefData),
    EnumConstant(Symbol, Option<NodeRef> /* value expr */),
    StaticAssert(NodeRef /* condition */, Symbol /* message */),

    // --- Top Level ---
    TranslationUnit(Vec<NodeRef> /* top-level declarations */),

    // --- Dummy Node ---
    Dummy,
}

// Structs for Large/Indirect Variants (to keep NodeKind size small and cache-friendly)
// These are stored separately with index-based references.

#[derive(Debug)]
pub struct IfStmt {
    pub condition: NodeRef,
    pub then_branch: NodeRef,
    pub else_branch: Option<NodeRef>,
}

#[derive(Debug)]
pub struct WhileStmt {
    pub condition: NodeRef,
    pub body: NodeRef,
}

#[derive(Debug)]
pub struct ForStmt {
    pub init: Option<NodeRef>, // Can be Declaration or Expression
    pub condition: Option<NodeRef>,
    pub increment: Option<NodeRef>,
    pub body: NodeRef,
}

#[derive(Debug)]
pub struct DeclarationData {
    pub specifiers: Vec<DeclSpecifier>,
    pub init_declarators: Vec<InitDeclarator>,
}

#[derive(Debug)]
pub struct InitDeclarator {
    pub declarator: Declarator,
    pub initializer: Option<Initializer>,
}

#[derive(Debug)]
pub struct FunctionDefData {
    pub specifiers: Vec<DeclSpecifier>,
    pub declarator: Declarator,
    pub body: NodeRef, // A CompoundStatement
}

#[derive(Debug)]
pub struct ParamData {
    pub specifiers: Vec<DeclSpecifier>,
    pub declarator: Option<Declarator>, // Optional name for abstract declarator
}

#[derive(Debug)]
pub struct RecordDefData {
    pub tag: Option<Symbol>,                   // None if anonymous
    pub members: Option<Vec<DeclarationData>>, // Field declarations
    pub is_union: bool,
}

#[derive(Debug)]
pub struct EnumDefData {
    pub tag: Option<Symbol>,
    pub enumerators: Option<Vec<NodeRef>>, // List of EnumConstant nodes
}

// Declaration Specifiers combine StorageClass, TypeQualifiers, FunctionSpecifiers, and TypeSpecifiers
#[derive(Debug)]
pub enum DeclSpecifier {
    StorageClass(StorageClass),
    TypeQualifiers(TypeQualifiers),
    FunctionSpecifiers(FunctionSpecifiers),
    AlignmentSpecifier(AlignmentSpecifier),
    TypeSpecifier(TypeSpecifier),
}

// Type Specifiers (C11)
#[derive(Debug)]
pub enum TypeSpecifier {
    Void,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
    Signed,
    Unsigned,
    Bool, // C11 _Bool
    Complex, // C11 _Complex
    Atomic(TypeRef), // C11 _Atomic
    Record(bool /* is_union */, Option<Symbol> /* tag */, Option<RecordDefData> /* definition */),
    Enum(Option<Symbol> /* tag */, Option<Vec<NodeRef>> /* enumerators */),
    TypedefName(Symbol),
}

// Storage Class Specifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageClass {
    Typedef,
    Extern,
    Static,
    Auto,
    Register,
    ThreadLocal, // C11 _Thread_local
}

// Type Qualifiers (using bitflags crate for consistency)
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct TypeQualifiers: u8 {
        const CONST = 1 << 0;
        const VOLATILE = 1 << 1;
        const RESTRICT = 1 << 2;
        const ATOMIC = 1 << 3; // C11 _Atomic
    }
}

// Function Specifiers (C11)
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct FunctionSpecifiers: u8 {
        const INLINE = 1 << 0;
        const NORETURN = 1 << 1; // C11 _Noreturn
    }
}

// Alignment Specifiers (C11 _Alignas)
#[derive(Debug)]
pub enum AlignmentSpecifier {
    Type(TypeRef), // _Alignas(type-name)
    Expr(NodeRef), // _Alignas(constant-expression)
}

// Unary Operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Minus,
    Deref,
    AddrOf,
    BitNot,
    LogicNot,
    PreIncrement,
    PreDecrement,
}

// Binary Operators (includes assignment types)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    LShift,
    RShift,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    LogicAnd,
    LogicOr,
    Comma,
    Assign,
    AssignAdd,
    AssignSub,
    AssignMul,
    AssignDiv,
    AssignMod,
    AssignBitAnd,
    AssignBitOr,
    AssignBitXor,
    AssignLShift,
    AssignRShift,
}

// C11 _Generic Association
#[derive(Debug)]
pub struct GenericAssociation {
    pub type_name: Option<TypeRef>, // None for 'default:'
    pub result_expr: NodeRef,
}

// Complex part of C declaration: the part that applies pointers, arrays, and functions
// This recursive structure allows for declarations like `int (*(*fp)())[10];`
#[derive(Debug)]
pub enum Declarator {
    Identifier(Symbol, TypeQualifiers, Option<Box<Declarator>>), // Base case: name (e.g., `x`)
    Pointer(TypeQualifiers, Option<Box<Declarator>>), // e.g., `*`
    Array(Box<Declarator>, ArraySize), // e.g., `[10]`
    Function(Box<Declarator>, Vec<ParamData> /* parameters */), // e.g., `(int x)`
    AnonymousRecord(bool /* is_union */, Vec<DeclarationData> /* members */), // C11 anonymous struct/union
}

// Defines array size (e.g., [10], [*], or [] for flexible array members)
#[derive(Debug)]
pub enum ArraySize {
    Expression(NodeRef),
    Star,                                              // [*] VLA
    Incomplete,                                        // []
    VlaSpecifier(Option<NodeRef> /* VLA size expr */), // `static` or `*` for VLA (C99)
}

// Initializer structure for variables (e.g., int x = 5; or struct s = {1, 2};)
#[derive(Debug)]
pub enum Initializer {
    Expression(NodeRef),              // = 5
    List(Vec<DesignatedInitializer>), // = { .x = 1, [0] = 2 }
}

// Designated initializer for array/struct lists (C99/C11)
#[derive(Debug)]
pub struct DesignatedInitializer {
    pub designation: Vec<Designator>,
    pub initializer: Initializer,
}

// A single designator in a list (.field or [index])
#[derive(Debug)]
pub enum Designator {
    FieldName(Symbol),
    ArrayIndex(NodeRef), // Index expression
}

// Type representation (for semantic analysis)
// This is a canonical type, distinct from TypeSpecifier which is a syntax construct.
// Types are stored in a separate Vec<Type> with TypeRef references.

#[derive(Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub qualifiers: TypeQualifiers,
    pub size: Option<usize>,      // Computed during semantic analysis
    pub alignment: Option<usize>, // Computed during semantic analysis
}

#[derive(Debug)]
pub enum TypeKind {
    Void,
    Bool,
    Char {
        is_signed: bool,
    },
    Short {
        is_signed: bool,
    },
    Int {
        is_signed: bool,
    },
    Long {
        is_signed: bool,
        is_long_long: bool,
    },
    Float,
    Double {
        is_long_double: bool,
    },
    Complex {
        base_type: TypeRef,
    }, // C11 _Complex
    Atomic {
        base_type: TypeRef,
    }, // C11 _Atomic
    Pointer {
        pointee: TypeRef,
    },
    Array {
        element_type: TypeRef,
        size: ArraySizeType,
    },
    Function {
        return_type: TypeRef,
        parameters: Vec<FunctionParameter>,
        is_variadic: bool,
    },
    Record {
        // Represents both struct and union
        tag: Option<Symbol>,
        members: Vec<StructMember>,
        is_complete: bool,
        is_union: bool, // Differentiate between struct and union
    },
    Enum {
        tag: Option<Symbol>,
        base_type: TypeRef, // Underlying integer type
        enumerators: Vec<EnumConstant>,
        is_complete: bool,
    },
    Typedef {
        name: Symbol,
        aliased_type: TypeRef,
    },
    // Placeholder for incomplete types during semantic analysis
    Incomplete,
    Error, // For error recovery
}

#[derive(Debug)]
pub enum ArraySizeType {
    Constant(usize),
    Variable(NodeRef), // VLA
    Incomplete,
    Star, // [*] for function parameters
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub param_type: TypeRef,
    pub name: Option<Symbol>,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: Symbol,
    pub member_type: TypeRef,
    pub bit_field_size: Option<usize>,
    pub location: SourceSpan,
}

#[derive(Debug)]
pub struct EnumConstant {
    pub name: Symbol,
    pub value: i64, // Resolved value
    pub location: SourceSpan,
}
```

## 4. Cache-Friendly Traversal and Operations

The flattened AST enables highly efficient traversal and operations:

-   **Linear Traversal**: The contiguous `Vec<Node>` allows for sequential memory access, maximizing cache hits during depth-first or breadth-first traversals.
-   **Index-Based Navigation**: Child nodes are accessed via simple array indexing (`nodes[index]`), avoiding pointer dereferences and improving branch prediction.
-   **SIMD-Enabled Operations**: The linear layout supports SIMD instructions for batch processing of node properties (e.g., checking node kinds or spans).
-   **Visitor Pattern**: Implement a visitor that iterates through the node array, using indices to navigate the tree structure efficiently.
-   **Data-Oriented Design (DOD)**: The flattened structure naturally supports DOD patterns - passes can iterate over slices of the node array, processing only relevant data contiguously.
-   **Parallel Processing**: The index-based references make it easier to parallelize traversals across subtrees without complex pointer management.

## 5. Implementation Notes

The AST implementation includes several practical enhancements over the basic design:

- **Interior Mutability**: Uses `Cell<Option<TypeRef>>` and `Cell<Option<SymbolEntryRef>>` for semantic annotations without requiring mutable AST references
- **Anonymous Records**: Support for C11 anonymous structs/unions in declarators
- **Raw Float Literals**: Float literals store raw text (`Symbol`) rather than parsed values for precision preservation
- **Comprehensive Type System**: Full C11 type system including complex types, atomics, and qualifiers
- **Error Recovery**: `Error` type kind for malformed constructs during parsing

This AST design prioritizes performance and cache efficiency, providing a robust and fast foundation for the C11 compiler.