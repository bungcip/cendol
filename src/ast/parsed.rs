use crate::{
    ast::{
        BinaryOp, FunctionSpec, NameId, PType, SourceSpan, StorageClass, StringLitRef, TypeQualifier, UnaryOp,
        literal::LitRef,
    },
    lang_options::Visibility,
    semantic::{ScopeId, TypeQuals},
};
use std::num::NonZeroU32;
use thin_vec::ThinVec;

/// Pragma pack kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize)]
pub enum PragmaPackKind {
    Push,
    PushSet(u8),
    Pop,
    Set(Option<u8>),
}

/// Pragma visibility kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize)]
pub enum PragmaVisibilityKind {
    Push(crate::lang_options::Visibility),
    Pop,
}

use super::PTypeArena;

/// Node reference type for referencing child nodes in ParsedAst.
pub type PNodeRef = NonZeroU32;

/// The parsed AST storage.
/// Produced by the Parser. Purely syntactic.
#[derive(Clone, Default)]
pub struct PAst {
    pub nodes: Vec<PNode>,
    pub parsed_types: PTypeArena,
}

impl PAst {
    pub(crate) fn new() -> Self {
        PAst::default()
    }

    pub(crate) fn push_node(&mut self, node: PNode) -> PNodeRef {
        let index = self.nodes.len() as u32 + 1;
        self.nodes.push(node);
        PNodeRef::new(index).expect("PNodeRef overflow")
    }

    pub(crate) fn get_node(&self, index: PNodeRef) -> &PNode {
        &self.nodes[(index.get() - 1) as usize]
    }

    pub(crate) fn replace_node(&mut self, old_node: PNodeRef, new_node: PNode) -> PNodeRef {
        let old_index = (old_node.get() - 1) as usize;
        self.nodes[old_index] = new_node;
        old_node
    }

    pub(crate) fn get_root(&self) -> PNodeRef {
        PNodeRef::new(1).expect("Parsed AST empty")
    }
}

#[derive(Debug, Clone)]
pub struct PNode {
    pub kind: PNodeKind,
    pub span: SourceSpan,
}

impl PNode {
    pub(crate) fn new(kind: PNodeKind, span: SourceSpan) -> Self {
        PNode { kind, span }
    }
}

#[derive(Debug, Clone)]
pub enum PNodeKind {
    // --- Literals ---
    Literal(LitRef),

    // --- Expressions ---
    Ident(NameId), // No symbol ref yet
    UnaryOp(UnaryOp, PNodeRef),
    BinaryOp(BinaryOp, PNodeRef, PNodeRef),
    TernaryOp(PNodeRef, PNodeRef, PNodeRef),
    GnuStatementExpr(PNodeRef, PNodeRef),

    PostIncrement(PNodeRef),
    PostDecrement(PNodeRef),

    Assignment(BinaryOp, PNodeRef, PNodeRef),
    FunctionCall(PNodeRef, Box<[PNodeRef]>),
    MemberAccess(PNodeRef, NameId, bool),
    IndexAccess(PNodeRef, PNodeRef),

    Cast(PType, PNodeRef),
    BuiltinVaArg(PType, PNodeRef),
    BuiltinOffsetof(PType, PNodeRef),
    BuiltinTypesCompatibleP(Box<(PType, PType)>),
    SizeOfExpr(PNodeRef),
    SizeOfType(PType),
    AlignOfExpr(PNodeRef),
    AlignOfType(PType),

    CompoundLiteral(PType, PNodeRef),
    GenericSelection(PNodeRef, Box<[PGenericAssoc]>),
    BuiltinChooseExpr(PNodeRef, PNodeRef, PNodeRef),
    BuiltinComplex(PNodeRef, PNodeRef),
    BuiltinBitCast(PType, PNodeRef),
    BuiltinConvertVector(PNodeRef, PType),

    // --- Statements ---
    CompoundStmt(Box<[PNodeRef]>, ScopeId),
    GnuLocalLabel(Box<[NameId]>),
    If(PIfStmt),
    While(PWhileStmt),
    DoWhile(PNodeRef, PNodeRef),
    For(PForStmt),

    Return(Option<PNodeRef>),
    Break,
    Continue,
    Goto(NameId),
    ComputedGoto(PNodeRef),
    LabelAddr(NameId),
    Label(NameId, PNodeRef),

    Switch(PNodeRef, PNodeRef),
    Case(PNodeRef, PNodeRef),
    CaseRange(PNodeRef, PNodeRef, PNodeRef),
    Default(PNodeRef),

    ExpressionStmt(Option<PNodeRef>),
    EmptyStmt,
    AsmStmt(Box<PAsmStmt>),

    // --- Declarations & Definitions ---
    Declaration(PDecl),
    FunctionDef(PFunctionDef),
    EnumConstant(NameId, Option<PNodeRef>),
    StaticAssert(PNodeRef, Option<PNodeRef>),

    // --- Top Level ---
    TranslationUnit(Box<[PNodeRef]>),

    // --- InitializerList ---
    InitializerList(Box<[PDesignatedInitializer]>),

    // --- Pragma Pack ---
    PragmaPack(PragmaPackKind),

    // --- Pragma Visibility ---
    PragmaVisibility(PragmaVisibilityKind),

    // --- Dummy Node ---
    Dummy,
}

#[derive(Debug, Clone)]
pub struct PIfStmt {
    pub condition: PNodeRef,
    pub then_branch: PNodeRef,
    pub else_branch: Option<PNodeRef>,
}

#[derive(Debug, Clone)]
pub struct PWhileStmt {
    pub condition: PNodeRef,
    pub body: PNodeRef,
}

#[derive(Debug, Clone)]
pub struct PForStmt {
    pub init: Option<PNodeRef>,
    pub condition: Option<PNodeRef>,
    pub increment: Option<PNodeRef>,
    pub body: PNodeRef,
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone)]
pub struct PInitDeclarator {
    pub declarator: super::DeclaratorRef,
    pub initializer: Option<PNodeRef>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct PAsmOperand {
    pub constraint: StringLitRef,
    pub expr: PNodeRef,
}

#[derive(Debug, Clone)]
pub struct PAsmStmt {
    pub template: StringLitRef,
    pub outputs: Vec<PAsmOperand>,
    pub inputs: Vec<PAsmOperand>,
    pub clobbers: Vec<StringLitRef>,
    pub is_volatile: bool,
}

#[derive(Debug, Clone)]
pub struct PDecl {
    pub specifiers: ThinVec<DeclSpec>,
    pub init_declarators: ThinVec<PInitDeclarator>,
}

#[derive(Debug, Clone)]
pub struct PFunctionDef {
    pub specifiers: ThinVec<DeclSpec>,
    pub declarator: super::DeclaratorRef,
    pub body: PNodeRef,
}

// Declaration specifiers and related types
#[derive(Debug, Clone)]
pub enum DeclSpec {
    StorageClass(StorageClass),
    TypeQualifier(TypeQualifier),
    FunctionSpec(FunctionSpec),
    AlignmentSpec(PAlignmentSpec, bool /* is_gnu */),
    TypeSpec(TypeSpec),
    Attribute,
    AttributePacked,
    AttributeCleanup(PNodeRef),
    AttributeTransparentUnion,
    AttributeVisibility(Visibility),
    AttributeAlias(StringLitRef),
    AttributeAsm(StringLitRef),
    AttributeMode(NameId),
}

// Type specifiers
#[derive(Debug, Clone)]
pub enum TypeSpec {
    Void,
    Char,
    Char8,
    Short,
    Int,
    Long,
    LongLong,
    // Combined types for parser correctness
    UnsignedLong,
    UnsignedLongLong,
    UnsignedShort,
    UnsignedChar,
    SignedChar,
    SignedShort,
    SignedLong,
    SignedLongLong,
    Float,
    Double,
    LongDouble,
    ComplexFloat,
    ComplexDouble,
    ComplexLongDouble,
    Signed,
    Unsigned,
    Bool,
    Complex,
    Atomic(PType), // _Bool, _Complex, _Atomic
    Record(
        bool,                  /* is_union */
        Option<NameId>,        /* tag */
        Option<Vec<PNodeRef>>, /* field members */
        Vec<DeclSpec>,         /* attributes */
    ),
    Enum(
        Option<NameId>,        /* tag */
        Option<Vec<PNodeRef>>, /* enumerators */
        Option<PType>,         /* underlying type */
    ),
    TypedefName(NameId),
    VaList,
    AutoType,
    Typeof(PType),
    TypeofExpr(PNodeRef),
    TypeofUnqual(PType),
    TypeofUnqualExpr(PNodeRef),
}

// Alignment specifiers
#[derive(Debug, Clone)]
pub enum PAlignmentSpec {
    Type(PType),    // _Alignas(type-name)
    Expr(PNodeRef), // _Alignas(constant-expression)
}

#[derive(Debug, Clone)]
pub struct PParam {
    pub name: Option<NameId>,
    pub ty: PType,
    pub storage: StorageClass,
    pub is_inline: bool,
    pub is_noreturn: bool,
    pub alignment: Option<PAlignmentSpec>,
    pub span: SourceSpan,
}

// Array sizes
#[derive(Debug, Clone)]
pub enum PArraySize {
    Expression {
        expr: PNodeRef,
        quals: TypeQuals,
    },
    Star {
        quals: TypeQuals,
    }, // [*] VLA
    Incomplete, // []
    VlaSpec {
        is_static: bool,
        quals: TypeQuals,
        size: Option<PNodeRef>,
    }, // for VLA
}

impl PArraySize {
    pub(crate) fn quals(&self) -> TypeQuals {
        match self {
            PArraySize::Expression { quals, .. } => *quals,
            PArraySize::Star { quals } => *quals,
            PArraySize::VlaSpec { quals, .. } => *quals,
            PArraySize::Incomplete => TypeQuals::empty(),
        }
    }

    pub(crate) fn is_static(&self) -> bool {
        match self {
            PArraySize::VlaSpec { is_static, .. } => *is_static,
            _ => false,
        }
    }

    pub(crate) fn is_star(&self) -> bool {
        matches!(self, PArraySize::Star { .. })
    }

    pub(crate) fn size_expr(&self) -> Option<PNodeRef> {
        match self {
            PArraySize::Expression { expr, .. } => Some(*expr),
            PArraySize::VlaSpec { size, .. } => *size,
            _ => None,
        }
    }
}

// Record definitions
#[derive(Debug, Clone)]
pub struct PGenericAssoc {
    pub type_name: Option<PType>, // None for 'default:'
    pub result_expr: PNodeRef,
}

#[derive(Debug, Clone)]
pub struct PDesignatedInitializer {
    pub designation: Box<[PDesignator]>,
    pub initializer: PNodeRef,
}

#[derive(Debug, Clone)]
pub enum PDesignator {
    FieldName(NameId),
    ArrayIndex(PNodeRef),
    ArrayRange(PNodeRef, PNodeRef),
}
impl DeclSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        match self {
            DeclSpec::AlignmentSpec(aspec, _) => aspec.for_each_child(f),
            DeclSpec::TypeSpec(ts) => ts.for_each_child(f),
            DeclSpec::AttributeCleanup(e) => f(*e),
            _ => {}
        }
    }
}

impl TypeSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        match self {
            TypeSpec::Enum(_, Some(enumerators), _) => {
                for &e in enumerators {
                    f(e);
                }
            }
            TypeSpec::Record(.., definition, attributes) => {
                if let Some(members) = definition {
                    for &m in members {
                        f(m);
                    }
                }
                for attr in attributes {
                    attr.for_each_child(f);
                }
            }
            TypeSpec::Typeof(_) => {}
            TypeSpec::TypeofExpr(expr) => {
                f(*expr);
            }
            TypeSpec::TypeofUnqual(_) => {}
            TypeSpec::TypeofUnqualExpr(expr) => {
                f(*expr);
            }
            _ => {}
        }
    }
}

impl PAlignmentSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        if let PAlignmentSpec::Expr(e) = self {
            f(*e)
        }
    }
}

impl PInitDeclarator {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        if let Some(init) = self.initializer {
            f(init);
        }
    }
}

impl PDecl {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        for init in &self.init_declarators {
            init.for_each_child(f);
        }
    }
}

impl PFunctionDef {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        f(self.body);
    }
}

impl PNodeKind {
    pub(super) fn tagname(&self) -> &'static str {
        match self {
            PNodeKind::Literal(_) => "Literal",
            PNodeKind::Ident(_) => "Ident",
            PNodeKind::UnaryOp(..) => "UnaryOp",
            PNodeKind::BinaryOp(..) => "BinaryOp",
            PNodeKind::TernaryOp(..) => "TernaryOp",
            PNodeKind::GnuStatementExpr(..) => "GnuStatementExpr",
            PNodeKind::PostIncrement(..) => "PostIncrement",
            PNodeKind::PostDecrement(..) => "PostDecrement",
            PNodeKind::Assignment(..) => "Assignment",
            PNodeKind::FunctionCall(..) => "FunctionCall",
            PNodeKind::MemberAccess(..) => "MemberAccess",
            PNodeKind::IndexAccess(..) => "IndexAccess",
            PNodeKind::Cast(..) => "Cast",
            PNodeKind::BuiltinVaArg(..) => "BuiltinVaArg",
            PNodeKind::BuiltinOffsetof(..) => "BuiltinOffsetof",
            PNodeKind::SizeOfExpr(..) => "SizeOfExpr",
            PNodeKind::SizeOfType(..) => "SizeOfType",
            PNodeKind::AlignOfExpr(..) => "AlignOfExpr",
            PNodeKind::AlignOfType(..) => "AlignOfType",
            PNodeKind::CompoundLiteral(..) => "CompoundLiteral",
            PNodeKind::GenericSelection(..) => "GenericSelection",
            PNodeKind::BuiltinChooseExpr(..) => "BuiltinChooseExpr",
            PNodeKind::CompoundStmt(..) => "CompoundStmt",
            PNodeKind::GnuLocalLabel(..) => "GnuLocalLabel",
            PNodeKind::If(..) => "If",
            PNodeKind::While(..) => "While",
            PNodeKind::DoWhile(..) => "DoWhile",
            PNodeKind::For(..) => "For",
            PNodeKind::Return(..) => "Return",
            PNodeKind::Break => "Break",
            PNodeKind::Continue => "Continue",
            PNodeKind::Goto(..) => "Goto",
            PNodeKind::ComputedGoto(..) => "ComputedGoto",
            PNodeKind::LabelAddr(..) => "LabelAddr",
            PNodeKind::Label(..) => "Label",
            PNodeKind::Switch(..) => "Switch",
            PNodeKind::Case(..) => "Case",
            PNodeKind::CaseRange(..) => "CaseRange",
            PNodeKind::Default(..) => "Default",
            PNodeKind::ExpressionStmt(..) => "ExpressionStmt",
            PNodeKind::EmptyStmt => "EmptyStmt",
            PNodeKind::AsmStmt(..) => "AsmStmt",
            PNodeKind::Declaration(..) => "Declaration",
            PNodeKind::FunctionDef(..) => "FunctionDef",
            PNodeKind::EnumConstant(..) => "EnumConstant",
            PNodeKind::StaticAssert(..) => "StaticAssert",
            PNodeKind::TranslationUnit(..) => "TranslationUnit",
            PNodeKind::InitializerList(..) => "InitializerList",
            PNodeKind::PragmaPack(..) => "PragmaPack",
            PNodeKind::PragmaVisibility(..) => "PragmaVisibility",
            PNodeKind::BuiltinComplex(..) => "BuiltinComplex",
            PNodeKind::BuiltinBitCast(..) => "BuiltinBitCast",
            PNodeKind::BuiltinConvertVector(..) => "BuiltinConvertVector",
            PNodeKind::BuiltinTypesCompatibleP(..) => "BuiltinTypesCompatibleP",
            PNodeKind::Dummy => "Dummy",
        }
    }

    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(PNodeRef)) {
        match self {
            PNodeKind::Literal(_)
            | PNodeKind::Ident(_)
            | PNodeKind::BuiltinTypesCompatibleP(_)
            | PNodeKind::SizeOfType(_)
            | PNodeKind::AlignOfType(_)
            | PNodeKind::Break
            | PNodeKind::Continue
            | PNodeKind::Goto(_)
            | PNodeKind::LabelAddr(_)
            | PNodeKind::EmptyStmt
            | PNodeKind::PragmaPack(_)
            | PNodeKind::PragmaVisibility(_)
            | PNodeKind::Dummy => {}
            PNodeKind::UnaryOp(_, e)
            | PNodeKind::PostIncrement(e)
            | PNodeKind::PostDecrement(e)
            | PNodeKind::MemberAccess(e, _, _)
            | PNodeKind::Cast(_, e)
            | PNodeKind::BuiltinVaArg(_, e)
            | PNodeKind::BuiltinBitCast(_, e)
            | PNodeKind::BuiltinOffsetof(_, e)
            | PNodeKind::SizeOfExpr(e)
            | PNodeKind::AlignOfExpr(e)
            | PNodeKind::CompoundLiteral(_, e)
            | PNodeKind::Label(_, e)
            | PNodeKind::ComputedGoto(e)
            | PNodeKind::Default(e)
            | PNodeKind::BuiltinConvertVector(e, _)
            | PNodeKind::GnuStatementExpr(e, _) => f(*e),
            PNodeKind::BinaryOp(_, l, r)
            | PNodeKind::Assignment(_, l, r)
            | PNodeKind::IndexAccess(l, r)
            | PNodeKind::BuiltinComplex(l, r)
            | PNodeKind::DoWhile(l, r)
            | PNodeKind::Switch(l, r)
            | PNodeKind::Case(l, r) => {
                f(*l);
                f(*r);
            }
            PNodeKind::StaticAssert(l, r) => {
                f(*l);
                if let Some(msg) = r {
                    f(*msg);
                }
            }
            PNodeKind::TernaryOp(c, t, e) | PNodeKind::CaseRange(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }

            PNodeKind::FunctionCall(c, args) => {
                f(*c);
                for a in args.as_ref() {
                    f(*a);
                }
            }
            PNodeKind::GenericSelection(c, assocs) => {
                f(*c);
                for a in assocs.as_ref() {
                    f(a.result_expr);
                }
            }
            PNodeKind::BuiltinChooseExpr(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }
            PNodeKind::CompoundStmt(stmts, _) | PNodeKind::TranslationUnit(stmts) => {
                for s in stmts.as_ref() {
                    f(*s);
                }
            }
            PNodeKind::If(stmt) => {
                f(stmt.condition);
                f(stmt.then_branch);
                if let Some(e) = stmt.else_branch {
                    f(e);
                }
            }
            PNodeKind::While(stmt) => {
                f(stmt.condition);
                f(stmt.body);
            }
            PNodeKind::For(stmt) => {
                if let Some(i) = stmt.init {
                    f(i);
                }
                if let Some(c) = stmt.condition {
                    f(c);
                }
                if let Some(i) = stmt.increment {
                    f(i);
                }
                f(stmt.body);
            }
            PNodeKind::Return(e) | PNodeKind::ExpressionStmt(e) => {
                if let Some(e) = e {
                    f(*e);
                }
            }
            PNodeKind::AsmStmt(e) => {
                for op in &e.outputs {
                    f(op.expr);
                }
                for op in &e.inputs {
                    f(op.expr);
                }
            }
            PNodeKind::EnumConstant(_, e) => {
                if let Some(e) = e {
                    f(*e);
                }
            }
            PNodeKind::Declaration(decl) => {
                decl.for_each_child(f);
            }
            PNodeKind::FunctionDef(data) => {
                data.for_each_child(f);
            }
            PNodeKind::InitializerList(inits) => {
                for init in inits.as_ref() {
                    f(init.initializer);
                    for d in init.designation.as_ref() {
                        match d {
                            PDesignator::ArrayIndex(idx) => f(*idx),
                            PDesignator::ArrayRange(s, e) => {
                                f(*s);
                                f(*e);
                            }
                            PDesignator::FieldName(_) => {}
                        }
                    }
                }
            }
            PNodeKind::GnuLocalLabel(_) => {}
        }
    }
}
