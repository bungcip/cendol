//! AST Node definitions, constructors, and builder patterns.
//!
//! This module contains the core AST node types, including the NodeKind enum
//! and associated data structures. It provides constructors and builder patterns
//! for creating complex AST nodes ergonomically.

use serde::Serialize;

use crate::{
    ast::{NameId, NodeRef, SymbolRef, TypeRef},
    semantic::{QualType, ScopeId},
};

/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
/// Maintained original structure for compatibility, but moved to this module.
use crate::ast::literal::Literal;

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    Literal(Literal),

    // --- Expressions ---
    // Ident now includes a resolved SymbolRef after semantic analysis
    Ident(NameId, SymbolRef),
    UnaryOp(UnaryOp, NodeRef),
    BinaryOp(BinaryOp, NodeRef, NodeRef),
    TernaryOp(NodeRef, NodeRef, NodeRef),
    StatementExpr(
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
    BuiltinOffsetof(QualType, NodeRef),
    BuiltinVaStart(NodeRef, NodeRef),
    BuiltinVaEnd(NodeRef),
    BuiltinVaCopy(NodeRef, NodeRef),
    BuiltinExpect(NodeRef, NodeRef),
    BuiltinMemcmp(NodeRef, NodeRef, NodeRef),
    BuiltinMemcpy(NodeRef, NodeRef, NodeRef),
    BuiltinMemset(NodeRef, NodeRef, NodeRef),
    BuiltinMemmove(NodeRef, NodeRef, NodeRef),
    BuiltinTypesCompatibleP(QualType, QualType),
    BuiltinPopcount(NodeRef),
    BuiltinPopcountL(NodeRef),
    BuiltinPopcountLL(NodeRef),
    BuiltinClz(NodeRef),
    BuiltinClzL(NodeRef),
    BuiltinClzLL(NodeRef),
    BuiltinCtz(NodeRef),
    BuiltinCtzL(NodeRef),
    BuiltinCtzLL(NodeRef),
    BuiltinFfs(NodeRef),
    BuiltinFfsL(NodeRef),
    BuiltinFfsLL(NodeRef),
    BuiltinBswap16(NodeRef),
    BuiltinBswap32(NodeRef),
    BuiltinBswap64(NodeRef),
    BuiltinFabs(NodeRef),
    BuiltinFabsf(NodeRef),
    BuiltinFabsl(NodeRef),
    BuiltinPrefetch(NodeRef, Option<NodeRef>, Option<NodeRef>),
    BuiltinAlloca(NodeRef),
    AtomicOp(AtomicOp, NodeRef /* args start */, u16 /* arg count */),
    SizeOfExpr(NodeRef),
    SizeOfType(QualType),
    AlignOfExpr(NodeRef),
    AlignOfType(QualType), // C11 _Alignof

    CompoundLiteral(QualType, NodeRef),
    GenericSelection(GenericSelection),
    GenericAssociation(GenericAssociation),
    BuiltinChooseExpr(NodeRef, NodeRef, NodeRef),
    BuiltinConstantP(NodeRef),
    BuiltinUnreachable,
    BuiltinTrap,

    // --- Statements (Complex statements are separate structs) ---
    CompoundStmt(CompoundStmt),
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

    ExpressionStmt(Option<NodeRef> /* expression */), // Expression followed by ';'
    AsmStmt(NodeRef),

    // --- Declarations & Definitions ---
    // Removed Parser-only Declaration and FunctionDef variants.
    // They are now lowered to semantic nodes immediately or exist only in ParsedAst.
    StaticAssert(NodeRef /* condition */, Option<NodeRef> /* message */),

    // --- Semantic Nodes (Type-Resolved) ---
    // declarations of VarDecl/FunctionDecl/TypedefDecl/RecordDecl
    VarDecl(VarDecl),
    FunctionDecl(FunctionDecl),
    TypedefDecl(TypedefDecl),
    RecordDecl(RecordDecl),
    FieldDecl(FieldDecl),
    EnumDecl(EnumDecl),
    EnumMember(EnumMember),
    Function(Function),
    Param(Param),

    // --- Top Level ---
    TranslationUnit(TranslationUnit),

    // --- InitializerList ---
    InitializerList(InitializerList),
    InitializerItem(DesignatedInitializer),
    Designator(Designator),

    // --- Dummy Node ---
    Dummy,
}

impl NodeKind {
    pub(super) fn tagname(&self) -> &'static str {
        match self {
            NodeKind::Literal(_) => "Literal",
            NodeKind::Ident(..) => "Ident",
            NodeKind::UnaryOp(..) => "UnaryOp",
            NodeKind::BinaryOp(..) => "BinaryOp",
            NodeKind::TernaryOp(..) => "TernaryOp",
            NodeKind::StatementExpr(..) => "GnuStatementExpr",
            NodeKind::PostIncrement(..) => "PostIncrement",
            NodeKind::PostDecrement(..) => "PostDecrement",
            NodeKind::Assignment(..) => "Assignment",
            NodeKind::FunctionCall(..) => "FunctionCall",
            NodeKind::MemberAccess(..) => "MemberAccess",
            NodeKind::IndexAccess(..) => "IndexAccess",
            NodeKind::Cast(..) => "Cast",
            NodeKind::BuiltinVaArg(..) => "BuiltinVaArg",
            NodeKind::BuiltinOffsetof(..) => "BuiltinOffsetof",
            NodeKind::BuiltinVaStart(..) => "BuiltinVaStart",
            NodeKind::BuiltinVaEnd(..) => "BuiltinVaEnd",
            NodeKind::BuiltinVaCopy(..) => "BuiltinVaCopy",
            NodeKind::BuiltinExpect(..) => "BuiltinExpect",
            NodeKind::BuiltinMemcmp(..) => "BuiltinMemcmp",
            NodeKind::BuiltinMemcpy(..) => "BuiltinMemcpy",
            NodeKind::BuiltinMemset(..) => "BuiltinMemset",
            NodeKind::BuiltinMemmove(..) => "BuiltinMemmove",
            NodeKind::BuiltinTypesCompatibleP(..) => "BuiltinTypesCompatibleP",
            NodeKind::BuiltinPopcount(..) => "BuiltinPopcount",
            NodeKind::BuiltinPopcountL(..) => "BuiltinPopcountL",
            NodeKind::BuiltinPopcountLL(..) => "BuiltinPopcountLL",
            NodeKind::BuiltinClz(..) => "BuiltinClz",
            NodeKind::BuiltinClzL(..) => "BuiltinClzL",
            NodeKind::BuiltinClzLL(..) => "BuiltinClzLL",
            NodeKind::BuiltinCtz(..) => "BuiltinCtz",
            NodeKind::BuiltinCtzL(..) => "BuiltinCtzL",
            NodeKind::BuiltinCtzLL(..) => "BuiltinCtzLL",
            NodeKind::BuiltinFfs(..) => "BuiltinFfs",
            NodeKind::BuiltinFfsL(..) => "BuiltinFfsL",
            NodeKind::BuiltinFfsLL(..) => "BuiltinFfsLL",
            NodeKind::BuiltinBswap16(..) => "BuiltinBswap16",
            NodeKind::BuiltinBswap32(..) => "BuiltinBswap32",
            NodeKind::BuiltinBswap64(..) => "BuiltinBswap64",
            NodeKind::BuiltinFabs(..) => "BuiltinFabs",
            NodeKind::BuiltinFabsf(..) => "BuiltinFabsf",
            NodeKind::BuiltinFabsl(..) => "BuiltinFabsl",
            NodeKind::BuiltinPrefetch(..) => "BuiltinPrefetch",
            NodeKind::BuiltinAlloca(..) => "BuiltinAlloca",
            NodeKind::AtomicOp(..) => "AtomicOp",
            NodeKind::SizeOfExpr(..) => "SizeOfExpr",
            NodeKind::SizeOfType(..) => "SizeOfType",
            NodeKind::AlignOfExpr(..) => "AlignOfExpr",
            NodeKind::AlignOfType(..) => "AlignOfType",
            NodeKind::CompoundLiteral(..) => "CompoundLiteral",
            NodeKind::GenericSelection(..) => "GenericSelection",
            NodeKind::GenericAssociation(..) => "GenericAssociation",
            NodeKind::BuiltinChooseExpr(..) => "BuiltinChooseExpr",
            NodeKind::BuiltinConstantP(..) => "BuiltinConstantP",
            NodeKind::BuiltinUnreachable => "BuiltinUnreachable",
            NodeKind::BuiltinTrap => "BuiltinTrap",
            NodeKind::CompoundStmt(..) => "CompoundStmt",
            NodeKind::If(..) => "If",
            NodeKind::While(..) => "While",
            NodeKind::DoWhile(..) => "DoWhile",
            NodeKind::For(..) => "For",
            NodeKind::Return(..) => "Return",
            NodeKind::Break => "Break",
            NodeKind::Continue => "Continue",
            NodeKind::Goto(..) => "Goto",
            NodeKind::Label(..) => "Label",
            NodeKind::Switch(..) => "Switch",
            NodeKind::Case(..) => "Case",
            NodeKind::CaseRange(..) => "CaseRange",
            NodeKind::Default(..) => "Default",
            NodeKind::ExpressionStmt(..) => "ExpressionStmt",
            NodeKind::AsmStmt(..) => "AsmStmt",
            NodeKind::StaticAssert(..) => "StaticAssert",
            NodeKind::VarDecl(..) => "VarDecl",
            NodeKind::FunctionDecl(..) => "FunctionDecl",
            NodeKind::TypedefDecl(..) => "TypedefDecl",
            NodeKind::RecordDecl(..) => "RecordDecl",
            NodeKind::FieldDecl(..) => "FieldDecl",
            NodeKind::EnumDecl(..) => "EnumDecl",
            NodeKind::EnumMember(..) => "EnumMember",
            NodeKind::Function(..) => "Function",
            NodeKind::Param(..) => "Param",
            NodeKind::TranslationUnit(..) => "TranslationUnit",
            NodeKind::InitializerList(..) => "InitializerList",
            NodeKind::InitializerItem(..) => "InitializerItem",
            NodeKind::Designator(..) => "Designator",
            NodeKind::Dummy => "Dummy",
        }
    }

    pub(crate) fn visit_children<F: FnMut(NodeRef)>(&self, mut f: F) {
        match self {
            NodeKind::Literal(_)
            | NodeKind::Ident(..)
            | NodeKind::SizeOfType(_)
            | NodeKind::AlignOfType(_)
            | NodeKind::BuiltinTypesCompatibleP(..)
            | NodeKind::BuiltinUnreachable
            | NodeKind::BuiltinTrap
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
            | NodeKind::BuiltinOffsetof(_, child)
            | NodeKind::BuiltinVaEnd(child)
            | NodeKind::BuiltinPopcount(child)
            | NodeKind::BuiltinPopcountL(child)
            | NodeKind::BuiltinPopcountLL(child)
            | NodeKind::BuiltinClz(child)
            | NodeKind::BuiltinClzL(child)
            | NodeKind::BuiltinClzLL(child)
            | NodeKind::BuiltinCtz(child)
            | NodeKind::BuiltinCtzL(child)
            | NodeKind::BuiltinCtzLL(child)
            | NodeKind::BuiltinFfs(child)
            | NodeKind::BuiltinFfsL(child)
            | NodeKind::BuiltinFfsLL(child)
            | NodeKind::BuiltinBswap16(child)
            | NodeKind::BuiltinBswap32(child)
            | NodeKind::BuiltinBswap64(child)
            | NodeKind::BuiltinFabs(child)
            | NodeKind::BuiltinFabsf(child)
            | NodeKind::BuiltinFabsl(child)
            | NodeKind::BuiltinConstantP(child)
            | NodeKind::SizeOfExpr(child)
            | NodeKind::AlignOfExpr(child)
            | NodeKind::CompoundLiteral(_, child)
            | NodeKind::Label(_, child, _)
            | NodeKind::Default(child) => f(*child),
            NodeKind::StaticAssert(child, msg) => {
                f(*child);
                if let Some(m) = msg {
                    f(*m);
                }
            }

            NodeKind::BuiltinPrefetch(addr, rw, locality) => {
                f(*addr);
                if let Some(rw) = rw {
                    f(*rw);
                }
                if let Some(locality) = locality {
                    f(*locality);
                }
            }
            NodeKind::BuiltinAlloca(child) => f(*child),

            NodeKind::BuiltinVaStart(lhs, rhs)
            | NodeKind::BuiltinVaCopy(lhs, rhs)
            | NodeKind::BuiltinExpect(lhs, rhs)
            | NodeKind::BinaryOp(_, lhs, rhs)
            | NodeKind::StatementExpr(lhs, rhs)
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

            NodeKind::BuiltinChooseExpr(c, t, e)
            | NodeKind::BuiltinMemcmp(c, t, e)
            | NodeKind::BuiltinMemcpy(c, t, e)
            | NodeKind::BuiltinMemset(c, t, e)
            | NodeKind::BuiltinMemmove(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
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

            NodeKind::CompoundStmt(cs) => {
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

            NodeKind::Return(expr) | NodeKind::ExpressionStmt(expr) => {
                if let Some(child) = expr {
                    f(*child);
                }
            }

            NodeKind::AsmStmt(expr) => f(*expr),

            NodeKind::VarDecl(data) => {
                if let Some(init) = data.init {
                    f(init);
                }
            }

            NodeKind::FunctionDecl(_) => {}

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
                Designator::ArrayRange(start, end) => {
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
pub(crate) struct IfStmt {
    pub(crate) condition: NodeRef,
    pub(crate) then_branch: NodeRef,
    pub(crate) else_branch: Option<NodeRef>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct WhileStmt {
    pub(crate) condition: NodeRef,
    pub(crate) body: NodeRef,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct ForStmt {
    pub(crate) init: Option<NodeRef>, // Can be Declaration or Expression
    pub(crate) condition: Option<NodeRef>,
    pub(crate) increment: Option<NodeRef>,
    pub(crate) body: NodeRef,
    pub(crate) scope_id: ScopeId,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct CompoundStmt {
    pub(crate) stmt_start: NodeRef,
    pub(crate) stmt_len: u16,
    pub(crate) scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct TranslationUnit {
    pub(crate) decl_start: NodeRef,
    pub(crate) decl_len: u16,
    pub(crate) scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct InitializerList {
    pub(crate) init_start: NodeRef,
    pub(crate) init_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct Function {
    pub(crate) symbol: SymbolRef,
    pub(crate) ty: TypeRef, // function type, not the return type
    pub(crate) is_noreturn: bool,
    pub(crate) param_start: NodeRef,
    pub(crate) param_len: u16,
    pub(crate) body: NodeRef, // compound statement
    pub(crate) scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct Param {
    pub(crate) symbol: SymbolRef,
    pub(crate) qt: QualType,
}

// Semantic node data structures (type-resolved)
#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct VarDecl {
    pub(crate) name: NameId,
    pub(crate) qt: QualType,
    pub(crate) storage: Option<StorageClass>,
    pub(crate) is_thread_local: bool,
    pub(crate) init: Option<NodeRef>,  // InitializerList or Expression
    pub(crate) alignment: Option<u16>, // Max alignment in bytes
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct FunctionDecl {
    pub(crate) name: NameId,
    pub(crate) ty: TypeRef,
    pub(crate) storage: Option<StorageClass>,
    pub(crate) scope_id: ScopeId,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct TypedefDecl {
    pub(crate) name: NameId,
    pub(crate) qt: QualType,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct RecordDecl {
    pub(crate) name: Option<NameId>,
    pub(crate) ty: TypeRef,
    pub(crate) member_start: NodeRef,
    /// index where FieldDecl located
    pub(crate) member_len: u16,

    pub(crate) is_union: bool,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct FieldDecl {
    pub(crate) name: Option<NameId>,
    pub(crate) qt: QualType, // object type
    pub(crate) alignment: Option<u32>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct CallExpr {
    pub(crate) callee: NodeRef,
    pub(crate) arg_start: NodeRef, // index where CallArg located
    pub(crate) arg_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct EnumDecl {
    pub(crate) name: Option<NameId>,
    pub(crate) ty: TypeRef,
    pub(crate) member_start: NodeRef,
    pub(crate) member_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct EnumMember {
    pub(crate) name: NameId,
    pub(crate) value: i64,
    pub(crate) init_expr: Option<NodeRef>,
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

impl StorageClass {
    pub(crate) fn as_str(&self) -> &'static str {
        match self {
            StorageClass::Typedef => "typedef",
            StorageClass::Extern => "extern",
            StorageClass::Static => "static",
            StorageClass::Auto => "auto",
            StorageClass::Register => "register",
            StorageClass::ThreadLocal => "_Thread_local",
        }
    }
}

// Function specifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum FunctionSpec {
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
    Real,
    Imag,
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

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct DesignatedInitializer {
    pub(crate) designator_start: NodeRef,
    pub(crate) designator_len: u16,
    pub(crate) initializer: NodeRef,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) enum Designator {
    FieldName(NameId),
    ArrayIndex(NodeRef),          // Index expression
    ArrayRange(NodeRef, NodeRef), // GCC extension: Range expression [start ... end]
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct GenericSelection {
    pub(crate) control: NodeRef,
    pub(crate) assoc_start: NodeRef,
    pub(crate) assoc_len: u16,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(crate) struct GenericAssociation {
    pub(crate) ty: Option<QualType>, // None for 'default:'
    pub(crate) result_expr: NodeRef,
}
