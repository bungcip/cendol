//! AST Node definitions, constructors, and builder patterns.
//!
//! This module contains the core AST node types, including the NodeKind enum
//! and associated data structures. It provides constructors and builder patterns
//! for creating complex AST nodes ergonomically.

use serde::Serialize;

use crate::semantic::TypeQualifiers;
use crate::{
    ast::{NameId, NodeRef, SymbolRef, TypeRef},
    semantic::{QualType, ScopeId},
};

/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
/// Maintained original structure for compatibility, but moved to this module.
use crate::ast::literal::Literal;

#[derive(Debug, Clone, Copy, Serialize)]
pub enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    Literal(Literal),

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

    MemberAccess(
        NodeRef, /* object */
        NameId,  /* field */
        bool,    /* is_arrow */
    ),
    IndexAccess(NodeRef /* array */, NodeRef /* index */),

    Cast(QualType, NodeRef),
    BuiltinVaArg(QualType, NodeRef),
    BuiltinVaStart(NodeRef, NodeRef),
    BuiltinVaEnd(NodeRef),
    BuiltinVaCopy(NodeRef, NodeRef),
    BuiltinExpect(NodeRef, NodeRef),
    AtomicOp(AtomicOp, NodeRef /* args start */, u16 /* arg count */),
    SizeOfExpr(NodeRef),
    SizeOfType(QualType),
    AlignOf(QualType), // C11 _Alignof

    CompoundLiteral(QualType, NodeRef),
    GenericSelection(GenericSelectionData),
    GenericAssociation(GenericAssociationData),

    // --- Statements (Complex statements are separate structs) ---
    CompoundStatement(CompoundStmtData),
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
    StaticAssert(NodeRef /* condition */, NodeRef /* message */),

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
    Param(ParamData),

    // --- Top Level ---
    TranslationUnit(TranslationUnitData),

    // --- InitializerList ---
    InitializerList(InitializerListData),
    InitializerItem(DesignatedInitializer),
    Designator(Designator),

    // --- Dummy Node ---
    Dummy,
}

impl NodeKind {
    pub(crate) fn visit_children<F: FnMut(NodeRef)>(&self, mut f: F) {
        match self {
            NodeKind::Literal(_)
            | NodeKind::Ident(..)
            | NodeKind::SizeOfType(_)
            | NodeKind::AlignOf(_)
            | NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(..)
            | NodeKind::TypedefDecl(_)
            | NodeKind::FieldDecl(_)
            | NodeKind::EnumMember(_)
            | NodeKind::Param(_)
            | NodeKind::Dummy => {}

            NodeKind::UnaryOp(_, child)
            | NodeKind::PostIncrement(child)
            | NodeKind::PostDecrement(child)
            | NodeKind::MemberAccess(child, ..)
            | NodeKind::Cast(_, child)
            | NodeKind::BuiltinVaArg(_, child)
            | NodeKind::BuiltinVaEnd(child)
            | NodeKind::SizeOfExpr(child)
            | NodeKind::CompoundLiteral(_, child)
            | NodeKind::Label(_, child, _)
            | NodeKind::Default(child)
            | NodeKind::StaticAssert(child, _) => f(*child),

            NodeKind::BuiltinVaStart(lhs, rhs)
            | NodeKind::BuiltinVaCopy(lhs, rhs)
            | NodeKind::BuiltinExpect(lhs, rhs)
            | NodeKind::BinaryOp(_, lhs, rhs)
            | NodeKind::GnuStatementExpression(lhs, rhs)
            | NodeKind::Assignment(_, lhs, rhs)
            | NodeKind::IndexAccess(lhs, rhs)
            | NodeKind::DoWhile(lhs, rhs)
            | NodeKind::Switch(lhs, rhs)
            | NodeKind::Case(lhs, rhs) => {
                f(*lhs);
                f(*rhs);
            }

            NodeKind::TernaryOp(c1, c2, c3) | NodeKind::CaseRange(c1, c2, c3) => {
                f(*c1);
                f(*c2);
                f(*c3);
            }

            NodeKind::FunctionCall(call) => {
                f(call.callee);
                for child in call.arg_start.range(call.arg_len) {
                    f(child);
                }
            }

            NodeKind::AtomicOp(_, args_start, args_len) => {
                for child in args_start.range(*args_len) {
                    f(child);
                }
            }

            NodeKind::GenericSelection(gs) => {
                f(gs.control);
                for child in gs.assoc_start.range(gs.assoc_len) {
                    f(child);
                }
            }

            NodeKind::GenericAssociation(ga) => {
                f(ga.result_expr);
            }

            NodeKind::CompoundStatement(cs) => {
                for child in cs.stmt_start.range(cs.stmt_len) {
                    f(child);
                }
            }

            NodeKind::If(stmt) => {
                f(stmt.condition);
                f(stmt.then_branch);
                if let Some(else_branch) = stmt.else_branch {
                    f(else_branch);
                }
            }

            NodeKind::While(stmt) => {
                f(stmt.condition);
                f(stmt.body);
            }

            NodeKind::For(stmt) => {
                if let Some(init) = stmt.init {
                    f(init);
                }
                if let Some(cond) = stmt.condition {
                    f(cond);
                }
                if let Some(inc) = stmt.increment {
                    f(inc);
                }
                f(stmt.body);
            }

            NodeKind::Return(expr) | NodeKind::ExpressionStatement(expr) | NodeKind::EnumConstant(_, expr) => {
                if let Some(child) = expr {
                    f(*child);
                }
            }

            NodeKind::VarDecl(data) => {
                if let Some(init) = data.init {
                    f(init);
                }
            }

            NodeKind::FunctionDecl(data) => {
                if let Some(body) = data.body {
                    f(body);
                }
            }

            NodeKind::RecordDecl(data) => {
                for child in data.member_start.range(data.member_len) {
                    f(child);
                }
            }

            NodeKind::EnumDecl(data) => {
                for child in data.member_start.range(data.member_len) {
                    f(child);
                }
            }

            NodeKind::Function(data) => {
                for child in data.param_start.range(data.param_len) {
                    f(child);
                }
                f(data.body);
            }

            NodeKind::TranslationUnit(data) => {
                for child in data.decl_start.range(data.decl_len) {
                    f(child);
                }
            }

            NodeKind::InitializerList(data) => {
                for child in data.init_start.range(data.init_len) {
                    f(child);
                }
            }

            NodeKind::InitializerItem(item) => {
                for designator in item.designator_start.range(item.designator_len) {
                    f(designator);
                }
                f(item.initializer);
            }

            NodeKind::Designator(d) => match d {
                Designator::ArrayIndex(idx) => f(*idx),
                Designator::GnuArrayRange(start, end) => {
                    f(*start);
                    f(*end);
                }
                Designator::FieldName(_) => {}
            },
        }
    }
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
    pub scope_id: ScopeId,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Copy, Serialize)]
pub struct CompoundStmtData {
    pub stmt_start: NodeRef,
    pub stmt_len: u16,
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct TranslationUnitData {
    pub decl_start: NodeRef,
    pub decl_len: u16,
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct InitializerListData {
    pub init_start: NodeRef,
    pub init_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct FunctionData {
    pub symbol: SymbolRef,
    pub ty: TypeRef, // function type, not the return type
    pub is_noreturn: bool,
    pub param_start: NodeRef,
    pub param_len: u16,
    pub body: NodeRef, // compound statement
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct ParamData {
    pub symbol: SymbolRef,
    pub ty: QualType,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Copy, Serialize)]
pub struct VarDeclData {
    pub name: NameId,
    pub ty: QualType,
    pub storage: Option<StorageClass>,
    pub init: Option<NodeRef>,  // InitializerList or Expression
    pub alignment: Option<u16>, // Max alignment in bytes
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct FunctionDeclData {
    pub name: NameId,
    pub ty: TypeRef,
    pub storage: Option<StorageClass>,
    pub body: Option<NodeRef>,
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct TypedefDeclData {
    pub name: NameId,
    pub ty: QualType,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct RecordDeclData {
    pub name: Option<NameId>,
    pub ty: TypeRef,
    pub member_start: NodeRef,
    /// index where FieldDecl located
    pub member_len: u16,

    pub is_union: bool,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct FieldDeclData {
    pub name: Option<NameId>,
    pub ty: QualType, // object type
    pub alignment: Option<u32>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct CallExpr {
    pub callee: NodeRef,
    pub arg_start: NodeRef, // index where CallArg located
    pub arg_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct EnumDeclData {
    pub name: Option<NameId>,
    pub ty: TypeRef,
    pub member_start: NodeRef,
    pub member_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct EnumMemberData {
    pub name: NameId,
    pub value: i64,
    pub init_expr: Option<NodeRef>,
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

// Function specifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum FunctionSpecifier {
    Inline,
    Noreturn, // C11 _Noreturn
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
pub enum AtomicOp {
    LoadN,
    StoreN,
    ExchangeN,
    CompareExchangeN,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
}

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

    pub(crate) fn without_assignment(&self) -> Option<BinaryOp> {
        match self {
            BinaryOp::AssignAdd => Some(BinaryOp::Add),
            BinaryOp::AssignSub => Some(BinaryOp::Sub),
            BinaryOp::AssignMul => Some(BinaryOp::Mul),
            BinaryOp::AssignDiv => Some(BinaryOp::Div),
            BinaryOp::AssignMod => Some(BinaryOp::Mod),
            BinaryOp::AssignBitAnd => Some(BinaryOp::BitAnd),
            BinaryOp::AssignBitOr => Some(BinaryOp::BitOr),
            BinaryOp::AssignBitXor => Some(BinaryOp::BitXor),
            BinaryOp::AssignLShift => Some(BinaryOp::LShift),
            BinaryOp::AssignRShift => Some(BinaryOp::RShift),
            _ => None,
        }
    }
}
// Array sizes
#[derive(Debug, Clone, Copy, Serialize)]
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

#[derive(Debug, Clone, Copy, Serialize)]
pub struct DesignatedInitializer {
    pub designator_start: NodeRef,
    pub designator_len: u16,
    pub initializer: NodeRef,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum Designator {
    FieldName(NameId),
    ArrayIndex(NodeRef),             // Index expression
    GnuArrayRange(NodeRef, NodeRef), // GCC extension: Range expression [start ... end]
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct GenericSelectionData {
    pub control: NodeRef,
    pub assoc_start: NodeRef,
    pub assoc_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct GenericAssociationData {
    pub ty: Option<QualType>, // None for 'default:'
    pub result_expr: NodeRef,
}
