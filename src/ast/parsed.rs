use crate::{
    ast::{
        AtomicOp, BinaryOp, FunctionSpec, NameId, ParsedType, SourceSpan, StorageClass, TypeQualifier, UnaryOp,
        literal::Literal,
    },
    semantic::TypeQualifiers,
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

    pub(crate) fn replace_node(&mut self, old_node_ref: ParsedNodeRef, new_node: ParsedNode) -> ParsedNodeRef {
        let old_index = (old_node_ref.get() - 1) as usize;
        self.nodes[old_index] = new_node;
        old_node_ref
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
    Literal(Literal),

    // --- Expressions ---
    Ident(NameId), // No symbol ref yet
    UnaryOp(UnaryOp, ParsedNodeRef),
    BinaryOp(BinaryOp, ParsedNodeRef, ParsedNodeRef),
    TernaryOp(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    GnuStatementExpr(ParsedNodeRef, ParsedNodeRef),

    PostIncrement(ParsedNodeRef),
    PostDecrement(ParsedNodeRef),

    Assignment(BinaryOp, ParsedNodeRef, ParsedNodeRef),
    FunctionCall(ParsedNodeRef, Vec<ParsedNodeRef>),
    MemberAccess(ParsedNodeRef, NameId, bool),
    IndexAccess(ParsedNodeRef, ParsedNodeRef),

    Cast(ParsedType, ParsedNodeRef),
    BuiltinVaArg(ParsedType, ParsedNodeRef),
    BuiltinOffsetof(ParsedType, ParsedNodeRef),
    BuiltinVaStart(ParsedNodeRef, ParsedNodeRef),
    BuiltinVaEnd(ParsedNodeRef),
    BuiltinVaCopy(ParsedNodeRef, ParsedNodeRef),
    BuiltinExpect(ParsedNodeRef, ParsedNodeRef),
    BuiltinTypesCompatibleP(ParsedType, ParsedType),
    BuiltinPopcount(ParsedNodeRef),
    BuiltinClz(ParsedNodeRef),
    BuiltinCtz(ParsedNodeRef),
    BuiltinFfs(ParsedNodeRef),
    BuiltinBswap16(ParsedNodeRef),
    BuiltinBswap32(ParsedNodeRef),
    BuiltinBswap64(ParsedNodeRef),
    AtomicOp(AtomicOp, Vec<ParsedNodeRef>),
    SizeOfExpr(ParsedNodeRef),
    SizeOfType(ParsedType),
    AlignOf(ParsedType),

    CompoundLiteral(ParsedType, ParsedNodeRef),
    GenericSelection(ParsedNodeRef, Vec<ParsedGenericAssociation>),
    BuiltinChooseExpr(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    BuiltinConstantP(ParsedNodeRef),
    BuiltinUnreachable,
    BuiltinTrap,

    // --- Statements ---
    CompoundStmt(Vec<ParsedNodeRef>),
    If(ParsedIfStmt),
    While(ParsedWhileStmt),
    DoWhile(ParsedNodeRef, ParsedNodeRef),
    For(ParsedForStmt),

    Return(Option<ParsedNodeRef>),
    Break,
    Continue,
    Goto(NameId),
    Label(NameId, ParsedNodeRef),

    Switch(ParsedNodeRef, ParsedNodeRef),
    Case(ParsedNodeRef, ParsedNodeRef),
    CaseRange(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    Default(ParsedNodeRef),

    ExpressionStmt(Option<ParsedNodeRef>),
    EmptyStmt,

    // --- Declarations & Definitions ---
    Declaration(ParsedDecl),
    FunctionDef(ParsedFunctionDef),
    EnumConstant(NameId, Option<ParsedNodeRef>),
    StaticAssert(ParsedNodeRef, ParsedNodeRef),

    // --- Top Level ---
    TranslationUnit(Vec<ParsedNodeRef>),

    // --- InitializerList ---
    InitializerList(Vec<ParsedDesignatedInitializer>),

    // --- Pragma Pack ---
    PragmaPack(PragmaPackKind),

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
}

#[derive(Debug, Clone)]
pub struct ParsedInitDeclarator {
    pub declarator: super::DeclaratorRef,
    pub initializer: Option<ParsedNodeRef>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct ParsedDecl {
    pub specifiers: ThinVec<ParsedDeclSpec>,
    pub init_declarators: ThinVec<ParsedInitDeclarator>,
}

#[derive(Debug, Clone)]
pub struct ParsedFunctionDef {
    pub specifiers: ThinVec<ParsedDeclSpec>,
    pub declarator: super::DeclaratorRef,
    pub body: ParsedNodeRef,
}

// Declaration specifiers and related types
#[derive(Debug, Clone)]
pub enum ParsedDeclSpec {
    StorageClass(StorageClass),
    TypeQualifier(TypeQualifier),
    FunctionSpec(FunctionSpec),
    AlignmentSpec(ParsedAlignmentSpec),
    TypeSpec(ParsedTypeSpec),
    Attribute,
}

// Type specifiers
#[derive(Debug, Clone)]
pub enum ParsedTypeSpec {
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
        bool,                    /* is_union */
        Option<NameId>,          /* tag */
        Option<ParsedRecordDef>, /* definition */
    ),
    Enum(
        Option<NameId>,             /* tag */
        Option<Vec<ParsedNodeRef>>, /* enumerators */
    ),
    TypedefName(NameId),
    VaList,
    AutoType,
    Typeof(ParsedType),
    TypeofExpr(ParsedNodeRef),
}

// Alignment specifiers
#[derive(Debug, Clone)]
pub enum ParsedAlignmentSpec {
    Type(ParsedType),    // _Alignas(type-name)
    Expr(ParsedNodeRef), // _Alignas(constant-expression)
}

// Declarators are now in parsed_types.rs and are arena-based (DeclaratorRef)

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

// Record definitions
#[derive(Debug, Clone)]
pub struct ParsedGenericAssociation {
    pub type_name: Option<ParsedType>, // None for 'default:'
    pub result_expr: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub struct ParsedRecordDef {
    pub tag: Option<NameId>,                 // None if anonymous
    pub members: Option<Vec<ParsedNodeRef>>, // Field declarations
    pub is_union: bool,
}

#[derive(Debug, Clone)]
pub struct ParsedDesignatedInitializer {
    pub designation: Vec<ParsedDesignator>,
    pub initializer: ParsedNodeRef,
}

#[derive(Debug, Clone)]
pub enum ParsedDesignator {
    FieldName(NameId),
    ArrayIndex(ParsedNodeRef),
    GnuArrayRange(ParsedNodeRef, ParsedNodeRef),
}
impl ParsedDeclSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedDeclSpec::AlignmentSpec(aspec) => aspec.for_each_child(f),
            ParsedDeclSpec::TypeSpec(ts) => ts.for_each_child(f),
            _ => {}
        }
    }
}

impl ParsedTypeSpec {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedTypeSpec::Enum(_, Some(enumerators)) => {
                for &e in enumerators {
                    f(e);
                }
            }
            ParsedTypeSpec::Record(_, _, Some(def)) => {
                if let Some(members) = &def.members {
                    for &m in members {
                        f(m);
                    }
                }
            }
            ParsedTypeSpec::Typeof(_) => {}
            ParsedTypeSpec::TypeofExpr(expr) => {
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
        // declarator is now a ref, we might need to recurse into it if it contains exprs
        // But most declarator exprs are array sizes which are already covered in AST nodes?
        // Actually, array sizes ARE expressions (ParsedNodeRef).
        f(self.body);
    }
}

impl ParsedNodeKind {
    pub(crate) fn tagname(&self) -> &'static str {
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
            ParsedNodeKind::BuiltinVaStart(..) => "BuiltinVaStart",
            ParsedNodeKind::BuiltinVaEnd(..) => "BuiltinVaEnd",
            ParsedNodeKind::BuiltinVaCopy(..) => "BuiltinVaCopy",
            ParsedNodeKind::BuiltinExpect(..) => "BuiltinExpect",
            ParsedNodeKind::BuiltinTypesCompatibleP(..) => "BuiltinTypesCompatibleP",
            ParsedNodeKind::BuiltinPopcount(..) => "BuiltinPopcount",
            ParsedNodeKind::BuiltinClz(..) => "BuiltinClz",
            ParsedNodeKind::BuiltinCtz(..) => "BuiltinCtz",
            ParsedNodeKind::BuiltinFfs(..) => "BuiltinFfs",
            ParsedNodeKind::BuiltinBswap16(..) => "BuiltinBswap16",
            ParsedNodeKind::BuiltinBswap32(..) => "BuiltinBswap32",
            ParsedNodeKind::BuiltinBswap64(..) => "BuiltinBswap64",
            ParsedNodeKind::AtomicOp(..) => "AtomicOp",
            ParsedNodeKind::SizeOfExpr(..) => "SizeOfExpr",
            ParsedNodeKind::SizeOfType(..) => "SizeOfType",
            ParsedNodeKind::AlignOf(..) => "AlignOf",
            ParsedNodeKind::CompoundLiteral(..) => "CompoundLiteral",
            ParsedNodeKind::GenericSelection(..) => "GenericSelection",
            ParsedNodeKind::BuiltinChooseExpr(..) => "BuiltinChooseExpr",
            ParsedNodeKind::BuiltinConstantP(..) => "BuiltinConstantP",
            ParsedNodeKind::BuiltinUnreachable => "BuiltinUnreachable",
            ParsedNodeKind::BuiltinTrap => "BuiltinTrap",
            ParsedNodeKind::CompoundStmt(..) => "CompoundStmt",
            ParsedNodeKind::If(..) => "If",
            ParsedNodeKind::While(..) => "While",
            ParsedNodeKind::DoWhile(..) => "DoWhile",
            ParsedNodeKind::For(..) => "For",
            ParsedNodeKind::Return(..) => "Return",
            ParsedNodeKind::Break => "Break",
            ParsedNodeKind::Continue => "Continue",
            ParsedNodeKind::Goto(..) => "Goto",
            ParsedNodeKind::Label(..) => "Label",
            ParsedNodeKind::Switch(..) => "Switch",
            ParsedNodeKind::Case(..) => "Case",
            ParsedNodeKind::CaseRange(..) => "CaseRange",
            ParsedNodeKind::Default(..) => "Default",
            ParsedNodeKind::ExpressionStmt(..) => "ExpressionStmt",
            ParsedNodeKind::EmptyStmt => "EmptyStmt",
            ParsedNodeKind::Declaration(..) => "Declaration",
            ParsedNodeKind::FunctionDef(..) => "FunctionDef",
            ParsedNodeKind::EnumConstant(..) => "EnumConstant",
            ParsedNodeKind::StaticAssert(..) => "StaticAssert",
            ParsedNodeKind::TranslationUnit(..) => "TranslationUnit",
            ParsedNodeKind::InitializerList(..) => "InitializerList",
            ParsedNodeKind::PragmaPack(..) => "PragmaPack",
            ParsedNodeKind::Dummy => "Dummy",
        }
    }

    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedNodeKind::Literal(_)
            | ParsedNodeKind::Ident(_)
            | ParsedNodeKind::BuiltinTypesCompatibleP(_, _)
            | ParsedNodeKind::SizeOfType(_)
            | ParsedNodeKind::AlignOf(_)
            | ParsedNodeKind::BuiltinUnreachable
            | ParsedNodeKind::BuiltinTrap
            | ParsedNodeKind::Break
            | ParsedNodeKind::Continue
            | ParsedNodeKind::Goto(_)
            | ParsedNodeKind::EmptyStmt
            | ParsedNodeKind::PragmaPack(_)
            | ParsedNodeKind::Dummy => {}
            ParsedNodeKind::UnaryOp(_, e)
            | ParsedNodeKind::PostIncrement(e)
            | ParsedNodeKind::PostDecrement(e)
            | ParsedNodeKind::MemberAccess(e, _, _)
            | ParsedNodeKind::Cast(_, e)
            | ParsedNodeKind::BuiltinVaArg(_, e)
            | ParsedNodeKind::BuiltinOffsetof(_, e)
            | ParsedNodeKind::BuiltinVaEnd(e)
            | ParsedNodeKind::BuiltinPopcount(e)
            | ParsedNodeKind::BuiltinClz(e)
            | ParsedNodeKind::BuiltinConstantP(e)
            | ParsedNodeKind::BuiltinCtz(e)
            | ParsedNodeKind::BuiltinFfs(e)
            | ParsedNodeKind::BuiltinBswap16(e)
            | ParsedNodeKind::BuiltinBswap32(e)
            | ParsedNodeKind::BuiltinBswap64(e)
            | ParsedNodeKind::SizeOfExpr(e)
            | ParsedNodeKind::CompoundLiteral(_, e)
            | ParsedNodeKind::Label(_, e)
            | ParsedNodeKind::Default(e)
            | ParsedNodeKind::GnuStatementExpr(e, _) => f(*e),
            ParsedNodeKind::BinaryOp(_, l, r)
            | ParsedNodeKind::Assignment(_, l, r)
            | ParsedNodeKind::IndexAccess(l, r)
            | ParsedNodeKind::BuiltinVaStart(l, r)
            | ParsedNodeKind::BuiltinVaCopy(l, r)
            | ParsedNodeKind::BuiltinExpect(l, r)
            | ParsedNodeKind::DoWhile(l, r)
            | ParsedNodeKind::Switch(l, r)
            | ParsedNodeKind::Case(l, r)
            | ParsedNodeKind::StaticAssert(l, r) => {
                f(*l);
                f(*r);
            }
            ParsedNodeKind::TernaryOp(c, t, e) | ParsedNodeKind::CaseRange(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }
            ParsedNodeKind::FunctionCall(c, args) => {
                f(*c);
                for a in args {
                    f(*a);
                }
            }
            ParsedNodeKind::AtomicOp(_, args) => {
                for a in args {
                    f(*a);
                }
            }
            ParsedNodeKind::GenericSelection(c, assocs) => {
                f(*c);
                for a in assocs {
                    f(a.result_expr);
                }
            }
            ParsedNodeKind::BuiltinChooseExpr(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }
            ParsedNodeKind::CompoundStmt(stmts) | ParsedNodeKind::TranslationUnit(stmts) => {
                for s in stmts {
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
                for init in inits {
                    f(init.initializer);
                    for d in &init.designation {
                        match d {
                            ParsedDesignator::ArrayIndex(idx) => f(*idx),
                            ParsedDesignator::GnuArrayRange(s, e) => {
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
