//! AST Node definitions, constructors, and builder patterns.
//!
//! This module contains the core AST node types, including the NodeKind enum
//! and associated data structures. It provides constructors and builder patterns
//! for creating complex AST nodes ergonomically.

use serde::Serialize;

use crate::semantic::TypeQualifiers;
use crate::{
    ast::{NameId, NodeRef, SymbolRef, TypeRef},
    semantic::QualType,
};

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
    // Ident now includes a resolved SymbolRef after semantic analysis
    Ident(NameId, SymbolRef),
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
    FunctionCall(CallExpr),
    CallArg(NodeRef),
    MemberAccess(
        NodeRef, /* object */
        NameId,  /* field */
        bool,    /* is_arrow */
    ),
    IndexAccess(NodeRef /* array */, NodeRef /* index */),

    Cast(QualType, NodeRef),
    SizeOfExpr(NodeRef),
    SizeOfType(QualType),
    AlignOf(QualType), // C11 _Alignof

    CompoundLiteral(QualType, NodeRef),
    GenericSelection(GenericSelectionData),
    GenericAssociation(GenericAssociationData),
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
    Goto(NameId, SymbolRef),                           // resolved symbol after semantic analysis
    Label(NameId, NodeRef /* statement */, SymbolRef), // resolved symbol after semantic analysis

    Switch(NodeRef /* condition */, NodeRef /* body statement */),
    Case(NodeRef /* const_expr */, NodeRef /* statement */),
    CaseRange(
        NodeRef, /* start_expr */
        NodeRef, /* end_expr */
        NodeRef, /* statement */
    ), // GNU Extension often supported
    Default(NodeRef /* statement */),

    ExpressionStatement(Option<NodeRef> /* expression */), // Expression followed by ';'

    // --- Declarations & Definitions ---
    // Removed Parser-only Declaration and FunctionDef variants.
    // They are now lowered to semantic nodes immediately or exist only in ParsedAst.
    EnumConstant(NameId, Option<NodeRef> /* value expr */),
    StaticAssert(NodeRef /* condition */, NameId /* message */),

    // --- Semantic Nodes (Type-Resolved) ---
    // declarations of VarDecl/FunctionDecl/TypedefDecl/RecordDecl
    VarDecl(VarDeclData),
    FunctionDecl(FunctionDeclData),
    TypedefDecl(TypedefDeclData),
    RecordDecl(RecordDeclData),
    FieldDecl(FieldDeclData),
    EnumDecl(EnumDeclData),
    EnumMember(EnumMemberData),
    Function(FunctionData),

    // --- Top Level ---
    TranslationUnit(Vec<NodeRef> /* top-level declarations */),

    // --- InitializerList ---
    InitializerList(Vec<DesignatedInitializer>),

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

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Serialize)]
pub struct FunctionData {
    pub symbol: SymbolRef,
    pub ty: TypeRef,            // function type, not the return type
    pub params: Vec<ParamDecl>, // normalized params
    pub body: NodeRef,          // compound statement
}

#[derive(Debug, Clone, Serialize)]
pub struct ParamDecl {
    pub symbol: SymbolRef,
    pub ty: QualType,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Serialize)]
pub struct VarDeclData {
    pub name: NameId,
    pub ty: QualType,
    pub storage: Option<StorageClass>,
    pub init: Option<NodeRef>,  // InitializerList or Expression
    pub alignment: Option<u32>, // Max alignment in bytes
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
    pub ty: QualType,
}

#[derive(Debug, Clone, Serialize)]
pub struct RecordDeclData {
    pub name: Option<NameId>,
    pub ty: TypeRef,
    pub member_start: NodeRef,
    /// index where FieldDecl located
    pub member_len: u16,

    pub is_union: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct FieldDeclData {
    pub name: Option<NameId>,
    pub ty: QualType, // object type
}

#[derive(Debug, Clone, Serialize)]
pub struct CallExpr {
    pub callee: NodeRef,
    pub arg_start: NodeRef, // index where CallArg located
    pub arg_len: u16,
}

#[derive(Debug, Clone, Serialize)]
pub struct EnumDeclData {
    pub name: Option<NameId>,
    pub ty: TypeRef,
    pub member_start: NodeRef,
    pub member_len: u16,
}

#[derive(Debug, Clone, Serialize)]
pub struct EnumMemberData {
    pub name: NameId,
    pub value: i64,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum TypeQualifier {
    Const,
    Restrict,
    Volatile,
    Atomic,
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

impl BinaryOp {
    pub(crate) fn is_assignment(&self) -> bool {
        matches!(
            self,
            BinaryOp::Assign
                | BinaryOp::AssignAdd
                | BinaryOp::AssignSub
                | BinaryOp::AssignMul
                | BinaryOp::AssignDiv
                | BinaryOp::AssignMod
                | BinaryOp::AssignBitAnd
                | BinaryOp::AssignBitOr
                | BinaryOp::AssignBitXor
                | BinaryOp::AssignLShift
                | BinaryOp::AssignRShift
        )
    }
}

// Function specifiers
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
    pub struct FunctionSpecifiers: u8 {
        const INLINE = 1 << 0;
        const NORETURN = 1 << 1; // C11 _Noreturn
    }
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

// Initializers
#[derive(Debug, Clone, Serialize)]
pub enum Initializer {
    Expression(NodeRef),              // = 5
    List(Vec<DesignatedInitializer>), // = { .x = 1, [0] = 2 }
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

#[derive(Debug, Clone, Serialize)]
pub struct GenericSelectionData {
    pub control: NodeRef,
    pub assoc_start: NodeRef,
    pub assoc_len: u16,
}

#[derive(Debug, Clone, Serialize)]
pub struct GenericAssociationData {
    pub ty: Option<QualType>, // None for 'default:'
    pub result_expr: NodeRef,
}
