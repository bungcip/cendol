//! AST Node definitions, constructors, and builder patterns.
//!
//! This module contains the core AST node types, including the NodeKind enum
//! and associated data structures. It provides constructors and builder patterns
//! for creating complex AST nodes ergonomically.

use serde::Serialize;
use std::cell::Cell;
use thin_vec::ThinVec;

use crate::ast::{NameId, NodeRef, SymbolRef, TypeRef};

/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
/// Maintained original structure for compatibility, but moved to this module.
#[derive(Debug, Clone, Serialize)]
pub enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    LiteralInt(i64), // Parsed integer literal value
    LiteralFloat(f64),
    LiteralString(NameId),
    LiteralChar(u8),

    // --- Expressions ---
    // Ident now includes a Cell for resolved SymbolEntry after semantic analysis
    Ident(NameId, Cell<Option<SymbolRef>>),
    UnaryOp(UnaryOp, NodeRef),
    BinaryOp(BinaryOp, NodeRef, NodeRef),
    TernaryOp(NodeRef, NodeRef, NodeRef),
    GnuStatementExpression(
        NodeRef, /* compound statement */
        NodeRef, /* result expression */
    ),

    PostIncrement(NodeRef),
    PostDecrement(NodeRef),

    Assignment(BinaryOp, NodeRef /* lhs */, NodeRef /* rhs */),
    FunctionCall(NodeRef /* func */, Vec<NodeRef> /* args */),
    MemberAccess(
        NodeRef,                 /* object */
        NameId,                  /* field */
        bool,                    /* is_arrow */
        Cell<Option<SymbolRef>>, /* resolved symbol after semantic analysis */
    ),
    IndexAccess(NodeRef /* array */, NodeRef /* index */),

    Cast(TypeRef, NodeRef),
    SizeOfExpr(NodeRef),
    SizeOfType(TypeRef),
    AlignOf(TypeRef), // C11 _Alignof

    CompoundLiteral(TypeRef, NodeRef),
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
    Goto(NameId, Cell<Option<SymbolRef>>), // resolved symbol after semantic analysis
    Label(NameId, NodeRef /* statement */, Cell<Option<SymbolRef>>), // resolved symbol after semantic analysis

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
    EnumConstant(NameId, Option<NodeRef> /* value expr */),
    StaticAssert(NodeRef /* condition */, NameId /* message */),

    // --- Semantic Nodes (Type-Resolved) ---
    // declarations of VarDecl/FunctionDecl/TypedefDecl/RecordDecl
    DeclarationList(Vec<NodeRef>),

    VarDecl(VarDeclData),
    FunctionDecl(FunctionDeclData),
    TypedefDecl(TypedefDeclData),
    RecordDecl(RecordDeclData),
    Function(FunctionData),

    // --- Top Level ---
    TranslationUnit(Vec<NodeRef> /* top-level declarations */),

    // --- InitializerList ---
    ListInitializer(Vec<DesignatedInitializer>), // TODO: rename to InitializerList

    // --- Dummy Node ---
    Dummy,
}

// Structs for Large/Indirect Variants (to keep NodeKind size small and cache-friendly)
// These are stored separately with index-based references.

// Control flow statements
#[derive(Debug, Clone, Copy, Serialize)]
pub struct IfStmt {
    pub condition: NodeRef,
    pub then_branch: NodeRef,
    pub else_branch: Option<NodeRef>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct WhileStmt {
    pub condition: NodeRef,
    pub body: NodeRef,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct ForStmt {
    pub init: Option<NodeRef>, // Can be Declaration or Expression
    pub condition: Option<NodeRef>,
    pub increment: Option<NodeRef>,
    pub body: NodeRef,
}

// Declaration data
#[derive(Debug, Clone, Serialize)]
pub struct DeclarationData {
    pub specifiers: ThinVec<DeclSpecifier>,
    pub init_declarators: ThinVec<InitDeclarator>,
}

#[derive(Debug, Clone, Serialize)]
pub struct InitDeclarator {
    pub declarator: Declarator,
    pub initializer: Option<NodeRef>, // Initializer or Expr
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionDefData {
    pub specifiers: ThinVec<DeclSpecifier>,
    pub declarator: Declarator,
    pub body: NodeRef, // A CompoundStatement
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Serialize)]
pub struct FunctionData {
    pub symbol: SymbolRef,
    pub ty: TypeRef,            // function type
    pub params: Vec<ParamDecl>, // normalized params
    pub body: NodeRef,          // compound statement
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamDecl {
    pub symbol: SymbolRef,
    pub ty: TypeRef,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Serialize)]
pub struct VarDeclData {
    pub name: NameId,
    pub ty: TypeRef,
    pub storage: Option<StorageClass>,
    pub init: Option<NodeRef>, // InitializerList or Expression
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionDeclData {
    pub name: NameId,
    pub ty: TypeRef,
    pub storage: Option<StorageClass>,
    pub body: Option<NodeRef>,
}

#[derive(Debug, Clone, Serialize)]
pub struct TypedefDeclData {
    pub name: NameId,
    pub ty: TypeRef,
}

#[derive(Debug, Clone, Serialize)]
pub struct RecordDeclData {
    pub name: Option<NameId>,
    pub ty: TypeRef,
    pub members: Vec<VarDeclData>,
    pub is_union: bool,
}

// Declaration specifiers and related types
#[derive(Debug, Clone, Serialize)]
pub enum DeclSpecifier {
    StorageClass(StorageClass),
    TypeQualifiers(TypeQualifiers),
    FunctionSpecifiers(FunctionSpecifiers),
    AlignmentSpecifier(AlignmentSpecifier),
    TypeSpecifier(TypeSpecifier),
    Attribute,
}

// Type specifiers
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
        Option<NameId>,        /* tag */
        Option<RecordDefData>, /* definition */
    ),
    Enum(
        Option<NameId>,       /* tag */
        Option<Vec<NodeRef>>, /* enumerators */
    ),
    TypedefName(NameId),
}

// Storage classes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum StorageClass {
    Typedef,
    Extern,
    Static,
    Auto,
    Register,
    ThreadLocal, // C11 _Thread_local
}

// Type qualifiers (imported from types module)
pub use super::types::TypeQualifiers;

// Unary Operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
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
#[repr(u8)]
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

// Function specifiers
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
    pub struct FunctionSpecifiers: u8 {
        const INLINE = 1 << 0;
        const NORETURN = 1 << 1; // C11 _Noreturn
    }
}

// Alignment specifiers
#[derive(Debug, Clone, Serialize)]
pub enum AlignmentSpecifier {
    Type(TypeRef), // _Alignas(type-name)
    Expr(NodeRef), // _Alignas(constant-expression)
}

// Declarators
#[derive(Debug, Clone, Serialize)]
pub enum Declarator {
    Identifier(NameId, TypeQualifiers, Option<Box<Declarator>>), // Base case: name (e.g., `x`)
    Abstract,                                                    // for abstract declarator
    Pointer(TypeQualifiers, Option<Box<Declarator>>),            // e.g., `*`
    Array(Box<Declarator>, ArraySize),                           // e.g., `[10]`
    Function {
        inner: Box<Declarator>,
        params: ThinVec<ParamData>,
        is_variadic: bool,
    }, // e.g., `(int x)`
    AnonymousRecord(bool /* is_union */, ThinVec<DeclarationData> /* members */), // C11 anonymous struct/union
    BitField(Box<Declarator>, NodeRef /* bit width expression */), // e.g., `x : 8`
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamData {
    pub specifiers: ThinVec<DeclSpecifier>,
    pub declarator: Option<Declarator>, // Optional name for abstract declarator
}

// Array sizes
#[derive(Debug, Clone, Serialize)]
pub enum ArraySize {
    Expression {
        expr: NodeRef,
        qualifiers: TypeQualifiers,
    },
    Star {
        qualifiers: TypeQualifiers,
    }, // [*] VLA
    Incomplete, // []
    VlaSpecifier {
        is_static: bool,
        qualifiers: TypeQualifiers,
        size: Option<NodeRef>,
    }, // for VLA
}

// Record definitions
#[derive(Debug, Clone, Serialize)]
pub struct RecordDefData {
    pub tag: Option<NameId>,                   // None if anonymous
    pub members: Option<Vec<DeclarationData>>, // Field declarations
    pub is_union: bool,
}

// Initializers
#[derive(Debug, Clone, Serialize)]
pub enum Initializer {
    Expression(NodeRef),              // = 5
    List(Vec<DesignatedInitializer>), // = { .x = 1, [0] = 2 }
}

impl Initializer {
    pub fn get_expression(&self) -> NodeRef {
        match self {
            Initializer::Expression(node_ref) => *node_ref,
            _ => panic!("Initializer is not an expression"),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DesignatedInitializer {
    pub designation: Vec<Designator>,
    pub initializer: NodeRef,
}

#[derive(Debug, Clone, Serialize)]
pub enum Designator {
    FieldName(NameId),
    ArrayIndex(NodeRef),             // Index expression
    GnuArrayRange(NodeRef, NodeRef), // GCC extension: Range expression [start ... end]
}

// Generic selection
#[derive(Debug, Clone, Serialize)]
pub struct GenericAssociation {
    pub type_name: Option<TypeRef>, // None for 'default:'
    pub result_expr: NodeRef,
}
