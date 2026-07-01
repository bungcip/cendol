use crate::{
    ast::{
        BinaryOp, FunctionSpec, NameId, ParsedType, SourceSpan, StorageClass, TypeQualifier, UnaryOp, literal::LitRef,
    },
    semantic::{ScopeId, TypeQualifiers},
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

use super::ParsedTypeArena;

/// Node reference type for referencing child nodes in ParsedAst.
pub type ParsedNodeRef = NonZeroU32;

/// The parsed AST storage.
/// Produced by the Parser. Purely syntactic.
#[derive(Clone, Default)]
pub struct ParsedAst {
    pub nodes: Vec<ParsedNode>,
    pub parsed_types: ParsedTypeArena,
}

impl ParsedAst {
    pub(crate) fn new() -> Self {
        ParsedAst::default()
    }

    pub(crate) fn push_node(&mut self, node: ParsedNode) -> ParsedNodeRef {
        let index = self.nodes.len() as u32 + 1;
        self.nodes.push(node);
        ParsedNodeRef::new(index).expect("ParsedNodeRef overflow")
    }

    pub(crate) fn get_node(&self, index: ParsedNodeRef) -> &ParsedNode {
        &self.nodes[(index.get() - 1) as usize]
    }

    pub(crate) fn replace_node(&mut self, old_node: ParsedNodeRef, new_node: ParsedNode) -> ParsedNodeRef {
        let old_index = (old_node.get() - 1) as usize;
        self.nodes[old_index] = new_node;
        old_node
    }

    pub(crate) fn get_root(&self) -> ParsedNodeRef {
        ParsedNodeRef::new(1).expect("Parsed AST empty")
    }
}

#[derive(Debug, Clone)]
pub struct ParsedNode {
    pub kind: ParsedNodeKind,
    pub span: SourceSpan,
}

impl ParsedNode {
    pub(crate) fn new(kind: ParsedNodeKind, span: SourceSpan) -> Self {
        ParsedNode { kind, span }
    }
}

#[derive(Debug, Clone)]
pub enum ParsedNodeKind {
    // --- Literals ---
    Literal(LitRef),

    // --- Expressions ---
    Ident(NameId), // No symbol ref yet
    UnaryOp(UnaryOp, ParsedNodeRef),
    BinaryOp(BinaryOp, ParsedNodeRef, ParsedNodeRef),
    TernaryOp(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    GnuStatementExpr(ParsedNodeRef, ParsedNodeRef),

    PostIncrement(ParsedNodeRef),
    PostDecrement(ParsedNodeRef),

    Assignment(BinaryOp, ParsedNodeRef, ParsedNodeRef),
    FunctionCall(ParsedNodeRef, Box<[ParsedNodeRef]>),
    MemberAccess(ParsedNodeRef, NameId, bool),
    IndexAccess(ParsedNodeRef, ParsedNodeRef),

    Cast(ParsedType, ParsedNodeRef),
    BuiltinVaArg(ParsedType, ParsedNodeRef),
    BuiltinOffsetof(ParsedType, ParsedNodeRef),
    BuiltinTypesCompatibleP(Box<(ParsedType, ParsedType)>),
    SizeOfExpr(ParsedNodeRef),
    SizeOfType(ParsedType),
    AlignOfExpr(ParsedNodeRef),
    AlignOfType(ParsedType),

    CompoundLiteral(ParsedType, ParsedNodeRef),
    GenericSelection(ParsedNodeRef, Box<[ParsedGenericAssociation]>),
    BuiltinChooseExpr(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    BuiltinComplex(ParsedNodeRef, ParsedNodeRef),
    BuiltinBitCast(ParsedType, ParsedNodeRef),
    BuiltinConvertVector(ParsedNodeRef, ParsedType),

    // --- Statements ---
    CompoundStmt(Box<[ParsedNodeRef]>, ScopeId),
    If(ParsedIfStmt),
    While(ParsedWhileStmt),
    DoWhile(ParsedNodeRef, ParsedNodeRef),
    For(ParsedForStmt),

    Return(Option<ParsedNodeRef>),
    Break,
    Continue,
    Goto(NameId),
    ComputedGoto(ParsedNodeRef),
    LabelAddr(NameId),
    Label(NameId, ParsedNodeRef),

    Switch(ParsedNodeRef, ParsedNodeRef),
    Case(ParsedNodeRef, ParsedNodeRef),
    CaseRange(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    Default(ParsedNodeRef),

    ExpressionStmt(Option<ParsedNodeRef>),
    EmptyStmt,
    AsmStmt(Box<ParsedAsmStmt>),

    // --- Declarations & Definitions ---
    Declaration(ParsedDecl),
    FunctionDef(ParsedFunctionDef),
    EnumConstant(NameId, Option<ParsedNodeRef>),
    StaticAssert(ParsedNodeRef, Option<ParsedNodeRef>),

    // --- Top Level ---
    TranslationUnit(Box<[ParsedNodeRef]>),

    // --- InitializerList ---
    InitializerList(Box<[ParsedDesignatedInitializer]>),

    // --- Pragma Pack ---
    PragmaPack(PragmaPackKind),

    // --- Pragma Visibility ---
    PragmaVisibility(PragmaVisibilityKind),

    // --- Dummy Node ---
    Dummy,
}

#[derive(Debug, Clone)]
pub struct ParsedIfStmt {
    pub condition: ParsedNodeRef,
    pub then_branch: ParsedNodeRef,
    pub else_branch: Option<ParsedNodeRef>,
}

#[derive(Debug, Clone)]
pub struct ParsedWhileStmt {
    pub condition: ParsedNodeRef,
    pub body: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub struct ParsedForStmt {
    pub init: Option<ParsedNodeRef>,
    pub condition: Option<ParsedNodeRef>,
    pub increment: Option<ParsedNodeRef>,
    pub body: ParsedNodeRef,
    pub scope_id: ScopeId,
}

#[derive(Debug, Clone)]
pub struct ParsedInitDeclarator {
    pub declarator: super::DeclaratorRef,
    pub initializer: Option<ParsedNodeRef>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct ParsedAsmOperand {
    pub constraint: LitRef,
    pub expr: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub struct ParsedAsmStmt {
    pub template: LitRef,
    pub outputs: Vec<ParsedAsmOperand>,
    pub inputs: Vec<ParsedAsmOperand>,
    pub clobbers: Vec<LitRef>,
    pub is_volatile: bool,
}

#[derive(Debug, Clone)]
pub struct ParsedDecl {
    pub specifiers: ThinVec<DeclSpec>,
    pub init_declarators: ThinVec<ParsedInitDeclarator>,
}

#[derive(Debug, Clone)]
pub struct ParsedFunctionDef {
    pub specifiers: ThinVec<DeclSpec>,
    pub declarator: super::DeclaratorRef,
    pub body: ParsedNodeRef,
}

// Declaration specifiers and related types
#[derive(Debug, Clone)]
pub enum DeclSpec {
    StorageClass(StorageClass),
    TypeQualifier(TypeQualifier),
    FunctionSpec(FunctionSpec),
    AlignmentSpec(ParsedAlignmentSpec, bool /* is_gnu */),
    TypeSpec(TypeSpec),
    Attribute,
    AttributePacked,
    AttributeCleanup(ParsedNodeRef),
    AttributeTransparentUnion,
    AttributeVisibility(crate::lang_options::Visibility),
}

// Type specifiers
#[derive(Debug, Clone)]
pub enum TypeSpec {
    Void,
    Char,
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
    Atomic(ParsedType), // _Bool, _Complex, _Atomic
    Record(
        bool,                       /* is_union */
        Option<NameId>,             /* tag */
        Option<Vec<ParsedNodeRef>>, /* field members */
        Vec<DeclSpec>,              /* attributes */
    ),
    Enum(
        Option<NameId>,             /* tag */
        Option<Vec<ParsedNodeRef>>, /* enumerators */
        Option<ParsedType>,         /* underlying type */
    ),
    TypedefName(NameId),
    VaList,
    AutoType,
    Typeof(ParsedType),
    TypeofExpr(ParsedNodeRef),
    TypeofUnqual(ParsedType),
    TypeofUnqualExpr(ParsedNodeRef),
}

// Alignment specifiers
#[derive(Debug, Clone)]
pub enum ParsedAlignmentSpec {
    Type(ParsedType),    // _Alignas(type-name)
    Expr(ParsedNodeRef), // _Alignas(constant-expression)
}

#[derive(Debug, Clone)]
pub struct ParsedParam {
    pub name: Option<NameId>,
    pub ty: ParsedType,
    pub storage: Option<StorageClass>,
    pub is_inline: bool,
    pub is_noreturn: bool,
    pub alignment: Option<ParsedAlignmentSpec>,
    pub span: SourceSpan,
}

// Array sizes
#[derive(Debug, Clone)]
pub enum ParsedArraySize {
    Expression {
        expr: ParsedNodeRef,
        qualifiers: TypeQualifiers,
    },
    Star {
        qualifiers: TypeQualifiers,
    }, // [*] VLA
    Incomplete, // []
    VlaSpec {
        is_static: bool,
        qualifiers: TypeQualifiers,
        size: Option<ParsedNodeRef>,
    }, // for VLA
}

impl ParsedArraySize {
    pub(crate) fn qualifiers(&self) -> TypeQualifiers {
        match self {
            ParsedArraySize::Expression { qualifiers, .. } => *qualifiers,
            ParsedArraySize::Star { qualifiers } => *qualifiers,
            ParsedArraySize::VlaSpec { qualifiers, .. } => *qualifiers,
            ParsedArraySize::Incomplete => TypeQualifiers::empty(),
        }
    }

    pub(crate) fn is_static(&self) -> bool {
        match self {
            ParsedArraySize::VlaSpec { is_static, .. } => *is_static,
            _ => false,
        }
    }

    pub(crate) fn is_star(&self) -> bool {
        matches!(self, ParsedArraySize::Star { .. })
    }

    pub(crate) fn size_expr(&self) -> Option<ParsedNodeRef> {
        match self {
            ParsedArraySize::Expression { expr, .. } => Some(*expr),
            ParsedArraySize::VlaSpec { size, .. } => *size,
            _ => None,
        }
    }
}

// Record definitions
#[derive(Debug, Clone)]
pub struct ParsedGenericAssociation {
    pub type_name: Option<ParsedType>, // None for 'default:'
    pub result_expr: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub struct ParsedDesignatedInitializer {
    pub designation: Box<[ParsedDesignator]>,
    pub initializer: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub enum ParsedDesignator {
    FieldName(NameId),
    ArrayIndex(ParsedNodeRef),
    ArrayRange(ParsedNodeRef, ParsedNodeRef),
}
impl DeclSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            DeclSpec::AlignmentSpec(aspec, _) => aspec.for_each_child(f),
            DeclSpec::TypeSpec(ts) => ts.for_each_child(f),
            DeclSpec::AttributeCleanup(e) => f(*e),
            _ => {}
        }
    }
}

impl TypeSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
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

impl ParsedAlignmentSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        if let ParsedAlignmentSpec::Expr(e) = self {
            f(*e)
        }
    }
}

impl ParsedInitDeclarator {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        if let Some(init) = self.initializer {
            f(init);
        }
    }
}

impl ParsedDecl {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        for init in &self.init_declarators {
            init.for_each_child(f);
        }
    }
}

impl ParsedFunctionDef {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        f(self.body);
    }
}

impl ParsedNodeKind {
    pub(super) fn tagname(&self) -> &'static str {
        match self {
            ParsedNodeKind::Literal(_) => "Literal",
            ParsedNodeKind::Ident(_) => "Ident",
            ParsedNodeKind::UnaryOp(..) => "UnaryOp",
            ParsedNodeKind::BinaryOp(..) => "BinaryOp",
            ParsedNodeKind::TernaryOp(..) => "TernaryOp",
            ParsedNodeKind::GnuStatementExpr(..) => "GnuStatementExpr",
            ParsedNodeKind::PostIncrement(..) => "PostIncrement",
            ParsedNodeKind::PostDecrement(..) => "PostDecrement",
            ParsedNodeKind::Assignment(..) => "Assignment",
            ParsedNodeKind::FunctionCall(..) => "FunctionCall",
            ParsedNodeKind::MemberAccess(..) => "MemberAccess",
            ParsedNodeKind::IndexAccess(..) => "IndexAccess",
            ParsedNodeKind::Cast(..) => "Cast",
            ParsedNodeKind::BuiltinVaArg(..) => "BuiltinVaArg",
            ParsedNodeKind::BuiltinOffsetof(..) => "BuiltinOffsetof",
            ParsedNodeKind::SizeOfExpr(..) => "SizeOfExpr",
            ParsedNodeKind::SizeOfType(..) => "SizeOfType",
            ParsedNodeKind::AlignOfExpr(..) => "AlignOfExpr",
            ParsedNodeKind::AlignOfType(..) => "AlignOfType",
            ParsedNodeKind::CompoundLiteral(..) => "CompoundLiteral",
            ParsedNodeKind::GenericSelection(..) => "GenericSelection",
            ParsedNodeKind::BuiltinChooseExpr(..) => "BuiltinChooseExpr",
            ParsedNodeKind::CompoundStmt(..) => "CompoundStmt",
            ParsedNodeKind::If(..) => "If",
            ParsedNodeKind::While(..) => "While",
            ParsedNodeKind::DoWhile(..) => "DoWhile",
            ParsedNodeKind::For(..) => "For",
            ParsedNodeKind::Return(..) => "Return",
            ParsedNodeKind::Break => "Break",
            ParsedNodeKind::Continue => "Continue",
            ParsedNodeKind::Goto(..) => "Goto",
            ParsedNodeKind::ComputedGoto(..) => "ComputedGoto",
            ParsedNodeKind::LabelAddr(..) => "LabelAddr",
            ParsedNodeKind::Label(..) => "Label",
            ParsedNodeKind::Switch(..) => "Switch",
            ParsedNodeKind::Case(..) => "Case",
            ParsedNodeKind::CaseRange(..) => "CaseRange",
            ParsedNodeKind::Default(..) => "Default",
            ParsedNodeKind::ExpressionStmt(..) => "ExpressionStmt",
            ParsedNodeKind::EmptyStmt => "EmptyStmt",
            ParsedNodeKind::AsmStmt(..) => "AsmStmt",
            ParsedNodeKind::Declaration(..) => "Declaration",
            ParsedNodeKind::FunctionDef(..) => "FunctionDef",
            ParsedNodeKind::EnumConstant(..) => "EnumConstant",
            ParsedNodeKind::StaticAssert(..) => "StaticAssert",
            ParsedNodeKind::TranslationUnit(..) => "TranslationUnit",
            ParsedNodeKind::InitializerList(..) => "InitializerList",
            ParsedNodeKind::PragmaPack(..) => "PragmaPack",
            ParsedNodeKind::PragmaVisibility(..) => "PragmaVisibility",
            ParsedNodeKind::BuiltinComplex(..) => "BuiltinComplex",
            ParsedNodeKind::BuiltinBitCast(..) => "BuiltinBitCast",
            ParsedNodeKind::BuiltinConvertVector(..) => "BuiltinConvertVector",
            ParsedNodeKind::BuiltinTypesCompatibleP(..) => "BuiltinTypesCompatibleP",
            ParsedNodeKind::Dummy => "Dummy",
        }
    }

    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedNodeKind::Literal(_)
            | ParsedNodeKind::Ident(_)
            | ParsedNodeKind::BuiltinTypesCompatibleP(_)
            | ParsedNodeKind::SizeOfType(_)
            | ParsedNodeKind::AlignOfType(_)
            | ParsedNodeKind::Break
            | ParsedNodeKind::Continue
            | ParsedNodeKind::Goto(_)
            | ParsedNodeKind::LabelAddr(_)
            | ParsedNodeKind::EmptyStmt
            | ParsedNodeKind::PragmaPack(_)
            | ParsedNodeKind::PragmaVisibility(_)
            | ParsedNodeKind::Dummy => {}
            ParsedNodeKind::UnaryOp(_, e)
            | ParsedNodeKind::PostIncrement(e)
            | ParsedNodeKind::PostDecrement(e)
            | ParsedNodeKind::MemberAccess(e, _, _)
            | ParsedNodeKind::Cast(_, e)
            | ParsedNodeKind::BuiltinVaArg(_, e)
            | ParsedNodeKind::BuiltinBitCast(_, e)
            | ParsedNodeKind::BuiltinOffsetof(_, e)
            | ParsedNodeKind::SizeOfExpr(e)
            | ParsedNodeKind::AlignOfExpr(e)
            | ParsedNodeKind::CompoundLiteral(_, e)
            | ParsedNodeKind::Label(_, e)
            | ParsedNodeKind::ComputedGoto(e)
            | ParsedNodeKind::Default(e)
            | ParsedNodeKind::BuiltinConvertVector(e, _)
            | ParsedNodeKind::GnuStatementExpr(e, _) => f(*e),
            ParsedNodeKind::BinaryOp(_, l, r)
            | ParsedNodeKind::Assignment(_, l, r)
            | ParsedNodeKind::IndexAccess(l, r)
            | ParsedNodeKind::BuiltinComplex(l, r)
            | ParsedNodeKind::DoWhile(l, r)
            | ParsedNodeKind::Switch(l, r)
            | ParsedNodeKind::Case(l, r) => {
                f(*l);
                f(*r);
            }
            ParsedNodeKind::StaticAssert(l, r) => {
                f(*l);
                if let Some(msg) = r {
                    f(*msg);
                }
            }
            ParsedNodeKind::TernaryOp(c, t, e) | ParsedNodeKind::CaseRange(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }

            ParsedNodeKind::FunctionCall(c, args) => {
                f(*c);
                for a in args.as_ref() {
                    f(*a);
                }
            }
            ParsedNodeKind::GenericSelection(c, assocs) => {
                f(*c);
                for a in assocs.as_ref() {
                    f(a.result_expr);
                }
            }
            ParsedNodeKind::BuiltinChooseExpr(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }
            ParsedNodeKind::CompoundStmt(stmts, _) | ParsedNodeKind::TranslationUnit(stmts) => {
                for s in stmts.as_ref() {
                    f(*s);
                }
            }
            ParsedNodeKind::If(stmt) => {
                f(stmt.condition);
                f(stmt.then_branch);
                if let Some(e) = stmt.else_branch {
                    f(e);
                }
            }
            ParsedNodeKind::While(stmt) => {
                f(stmt.condition);
                f(stmt.body);
            }
            ParsedNodeKind::For(stmt) => {
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
            ParsedNodeKind::Return(e) | ParsedNodeKind::ExpressionStmt(e) => {
                if let Some(e) = e {
                    f(*e);
                }
            }
            ParsedNodeKind::AsmStmt(e) => {
                for op in &e.outputs {
                    f(op.expr);
                }
                for op in &e.inputs {
                    f(op.expr);
                }
            }
            ParsedNodeKind::EnumConstant(_, e) => {
                if let Some(e) = e {
                    f(*e);
                }
            }
            ParsedNodeKind::Declaration(decl) => {
                decl.for_each_child(f);
            }
            ParsedNodeKind::FunctionDef(data) => {
                data.for_each_child(f);
            }
            ParsedNodeKind::InitializerList(inits) => {
                for init in inits.as_ref() {
                    f(init.initializer);
                    for d in init.designation.as_ref() {
                        match d {
                            ParsedDesignator::ArrayIndex(idx) => f(*idx),
                            ParsedDesignator::ArrayRange(s, e) => {
                                f(*s);
                                f(*e);
                            }
                            ParsedDesignator::FieldName(_) => {}
                        }
                    }
                }
            }
        }
    }
}
