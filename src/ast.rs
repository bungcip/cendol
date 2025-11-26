use bitflags::bitflags;
use std::cell::Cell;
use std::num::NonZeroU32;

/// Represents an interned string using symbol_table crate.
/// Alias for GlobalSymbol from symbol_table crate with global feature.
pub type Symbol = symbol_table::GlobalSymbol;

pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};

/// The flattened AST storage.
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
impl Default for Ast {
    fn default() -> Self {
        Self::new()
    }
}

impl Ast {
    pub fn new() -> Self {
        Ast {
            nodes: Vec::new(),
            types: Vec::new(),
            symbol_entries: Vec::new(),
            initializers: Vec::new(),
            root: None,
        }
    }

    pub fn get_root_node(&self) -> Option<&Node> {
        self.root.map(|node_ref| self.get_node(node_ref))
    }

    pub fn set_root_node(&mut self, node_ref: NodeRef) {
        self.root = Some(node_ref);
    }

    pub fn push_node(&mut self, node: Node) -> NodeRef {
        let index = self.nodes.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.nodes.push(node);
        NodeRef::new(index).expect("NodeRef overflow")
    }

    pub fn get_node(&self, index: NodeRef) -> &Node {
        &self.nodes[(index.get() - 1) as usize]
    }

    pub fn push_type(&mut self, ty: Type) -> TypeRef {
        let index = self.types.len() as u32 + 1;
        self.types.push(ty);
        TypeRef::new(index).expect("TypeRef overflow")
    }

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

    pub fn push_symbol_entry(&mut self, entry: SymbolEntry) -> SymbolEntryRef {
        let index = self.symbol_entries.len() as u32 + 1;
        self.symbol_entries.push(entry);
        SymbolEntryRef::new(index).expect("SymbolEntryRef overflow")
    }

    pub fn get_symbol_entry(&self, index: SymbolEntryRef) -> &SymbolEntry {
        &self.symbol_entries[(index.get() - 1) as usize]
    }

    pub fn push_initializer(&mut self, init: Initializer) -> InitializerRef {
        let index = self.initializers.len() as u32 + 1;
        self.initializers.push(init);
        InitializerRef::new(index).expect("InitializerRef overflow")
    }

    pub fn get_initializer(&self, index: InitializerRef) -> &Initializer {
        &self.initializers[(index.get() - 1) as usize]
    }
}

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

impl Node {
    pub fn new(kind: NodeKind, span: SourceSpan) -> Self {
        Node {
            kind,
            span,
            resolved_symbol: Cell::new(None),
            resolved_type: Cell::new(None),
        }
    }
}

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol entries are stored in a separate Vec<SymbolEntry> with SymbolEntryIndex references.
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

use serde::Serialize;
/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
#[derive(Debug, Clone, Serialize)]
pub enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    LiteralInt(i64), // Parsed integer literal value
    LiteralFloat(f64),
    LiteralString(Symbol),
    LiteralChar(char),

    // --- Expressions ---
    // Ident now includes a Cell for resolved SymbolEntry after semantic analysis
    Ident(Symbol, Cell<Option<SymbolEntryRef>>),
    UnaryOp(UnaryOp, NodeRef),
    BinaryOp(BinaryOp, NodeRef, NodeRef),
    TernaryOp(NodeRef, NodeRef, NodeRef),

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

    Switch(
        NodeRef, /* condition */
        NodeRef, /* body statement */
    ),
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

#[derive(Debug, Clone, Serialize)]
pub struct IfStmt {
    pub condition: NodeRef,
    pub then_branch: NodeRef,
    pub else_branch: Option<NodeRef>,
}

#[derive(Debug, Clone, Serialize)]
pub struct WhileStmt {
    pub condition: NodeRef,
    pub body: NodeRef,
}

#[derive(Debug, Clone, Serialize)]
pub struct ForStmt {
    pub init: Option<NodeRef>, // Can be Declaration or Expression
    pub condition: Option<NodeRef>,
    pub increment: Option<NodeRef>,
    pub body: NodeRef,
}

#[derive(Debug, Clone, Serialize)]
pub struct DeclarationData {
    pub specifiers: Vec<DeclSpecifier>,
    pub init_declarators: Vec<InitDeclarator>,
}

#[derive(Debug, Clone, Serialize)]
pub struct InitDeclarator {
    pub declarator: Declarator,
    pub initializer: Option<Initializer>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionDefData {
    pub specifiers: Vec<DeclSpecifier>,
    pub declarator: Declarator,
    pub body: NodeRef, // A CompoundStatement
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamData {
    pub specifiers: Vec<DeclSpecifier>,
    pub declarator: Option<Declarator>, // Optional name for abstract declarator
}

#[derive(Debug, Clone, Serialize)]
pub struct RecordDefData {
    pub tag: Option<Symbol>,                   // None if anonymous
    pub members: Option<Vec<DeclarationData>>, // Field declarations
    pub is_union: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct EnumDefData {
    pub tag: Option<Symbol>,
    pub enumerators: Option<Vec<NodeRef>>, // List of EnumConstant nodes
}

// Declaration Specifiers combine StorageClass, TypeQualifiers, FunctionSpecifiers, and TypeSpecifiers
#[derive(Debug, Clone, Serialize)]
pub struct DeclSpecifier {
    pub storage_class: Option<StorageClass>,
    pub type_qualifiers: TypeQualifiers,
    pub function_specifiers: FunctionSpecifiers,
    pub alignment_specifier: Option<AlignmentSpecifier>,
    pub type_specifier: TypeSpecifier,
}

// Type Specifiers (C11)
#[derive(Debug, Clone, Serialize)]
pub enum TypeSpecifier {
    Void,
    Char,
    Short,
    Int,
    Long,
    LongLong,
    Float,
    Double,
    LongDouble,
    Signed,
    Unsigned,
    Bool,
    Complex,
    Atomic(TypeRef), // _Bool, _Complex, _Atomic
    Record(
        bool,                  /* is_union */
        Option<Symbol>,        /* tag */
        Option<RecordDefData>, /* definition */
    ),
    Enum(
        Option<Symbol>,       /* tag */
        Option<Vec<NodeRef>>, /* enumerators */
    ),
    TypedefName(Symbol),
}

// Storage Class Specifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum StorageClass {
    Typedef,
    Extern,
    Static,
    Auto,
    Register,
    ThreadLocal, // C11 _Thread_local
}

// Type Qualifiers (using bitflags crate for consistency)
bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
    pub struct TypeQualifiers: u8 {
        const CONST = 1 << 0;
        const VOLATILE = 1 << 1;
        const RESTRICT = 1 << 2;
        const ATOMIC = 1 << 3; // C11 _Atomic
    }
}

// Function Specifiers (C11)
bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
    pub struct FunctionSpecifiers: u8 {
        const INLINE = 1 << 0;
        const NORETURN = 1 << 1; // C11 _Noreturn
    }
}

// Alignment Specifiers (C11 _Alignas)
#[derive(Debug, Clone, Serialize)]
pub enum AlignmentSpecifier {
    Type(TypeRef), // _Alignas(type-name)
    Expr(NodeRef), // _Alignas(constant-expression)
}

// Unary Operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
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
#[derive(Debug, Clone, Serialize)]
pub struct GenericAssociation {
    pub type_name: Option<TypeRef>, // None for 'default:'
    pub result_expr: NodeRef,
}

// Complex part of C declaration: the part that applies pointers, arrays, and functions
// This recursive structure allows for declarations like `int (*(*fp)())[10];`
#[derive(Debug, Clone, Serialize)]
pub enum Declarator {
    Identifier(Symbol, TypeQualifiers, Option<Box<Declarator>>), // Base case: name (e.g., `x`)
    Abstract,                                                    // for abstract declarator
    Pointer(TypeQualifiers, Option<Box<Declarator>>),            // e.g., `*`
    Array(Box<Declarator>, ArraySize),                           // e.g., `[10]`
    Function(Box<Declarator>, Vec<ParamData> /* parameters */),  // e.g., `(int x)`
    AnonymousRecord(
        bool,                 /* is_union */
        Vec<DeclarationData>, /* members */
    ), // C11 anonymous struct/union
}

// Defines array size (e.g., [10], [*], or [] for flexible array members)
#[derive(Debug, Clone, Serialize)]
pub enum ArraySize {
    Expression { expr: NodeRef, qualifiers: TypeQualifiers },
    Star { qualifiers: TypeQualifiers }, // [*] VLA
    Incomplete,                                        // []
    VlaSpecifier { is_static: bool, qualifiers: TypeQualifiers, size: Option<NodeRef> }, // for VLA
}

// Initializer structure for variables (e.g., int x = 5; or struct s = {1, 2};)
#[derive(Debug, Clone, Serialize)]
pub enum Initializer {
    Expression(NodeRef),              // = 5
    List(Vec<DesignatedInitializer>), // = { .x = 1, [0] = 2 }
}

// Designated initializer for array/struct lists (C99/C11)
#[derive(Debug, Clone, Serialize)]
pub struct DesignatedInitializer {
    pub designation: Vec<Designator>,
    pub initializer: Initializer,
}

// A single designator in a list (.field or [index])
#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone)]
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
