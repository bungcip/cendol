use crate::{
    ast::{
        AtomicOp, BinaryOp, FunctionSpecifier, NameId, ParsedType, SourceSpan, StorageClass, TypeQualifier, UnaryOp,
    },
    semantic::TypeQualifiers,
};
use std::num::NonZeroU32;
use thin_vec::ThinVec;

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
    Literal(crate::ast::literal::Literal),

    // --- Expressions ---
    Ident(NameId), // No symbol ref yet
    UnaryOp(UnaryOp, ParsedNodeRef),
    BinaryOp(BinaryOp, ParsedNodeRef, ParsedNodeRef),
    TernaryOp(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    GnuStatementExpression(ParsedNodeRef, ParsedNodeRef),

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
    AtomicOp(AtomicOp, Vec<ParsedNodeRef>),
    SizeOfExpr(ParsedNodeRef),
    SizeOfType(ParsedType),
    AlignOf(ParsedType),

    CompoundLiteral(ParsedType, ParsedNodeRef),
    GenericSelection(ParsedNodeRef, Vec<ParsedGenericAssociation>),
    BuiltinChooseExpr(ParsedNodeRef, ParsedNodeRef, ParsedNodeRef),
    BuiltinConstantP(ParsedNodeRef),

    // --- Statements ---
    CompoundStatement(Vec<ParsedNodeRef>),
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

    ExpressionStatement(Option<ParsedNodeRef>),
    EmptyStatement,

    // --- Declarations & Definitions ---
    Declaration(ParsedDeclarationData),
    FunctionDef(ParsedFunctionDefData),
    EnumConstant(NameId, Option<ParsedNodeRef>),
    StaticAssert(ParsedNodeRef, ParsedNodeRef),

    // --- Top Level ---
    TranslationUnit(Vec<ParsedNodeRef>),

    // --- InitializerList ---
    InitializerList(Vec<ParsedDesignatedInitializer>),

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
    pub declarator: ParsedDeclarator,
    pub initializer: Option<ParsedNodeRef>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct ParsedDeclarationData {
    pub specifiers: ThinVec<ParsedDeclSpecifier>,
    pub init_declarators: ThinVec<ParsedInitDeclarator>,
}

#[derive(Debug, Clone)]
pub struct ParsedFunctionDefData {
    pub specifiers: ThinVec<ParsedDeclSpecifier>,
    pub declarator: Box<ParsedDeclarator>,
    pub body: ParsedNodeRef,
}

// Declaration specifiers and related types
#[derive(Debug, Clone)]
pub enum ParsedDeclSpecifier {
    StorageClass(StorageClass),
    TypeQualifier(TypeQualifier),
    FunctionSpecifier(FunctionSpecifier),
    AlignmentSpecifier(ParsedAlignmentSpecifier),
    TypeSpecifier(ParsedTypeSpecifier),
    Attribute,
}

// Type specifiers
#[derive(Debug, Clone)]
pub enum ParsedTypeSpecifier {
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
        bool,                        /* is_union */
        Option<NameId>,              /* tag */
        Option<ParsedRecordDefData>, /* definition */
    ),
    Enum(
        Option<NameId>,             /* tag */
        Option<Vec<ParsedNodeRef>>, /* enumerators */
    ),
    TypedefName(NameId),
    VaList,
    Typeof(ParsedType),
    TypeofExpr(ParsedNodeRef),
}

// Alignment specifiers
#[derive(Debug, Clone)]
pub enum ParsedAlignmentSpecifier {
    Type(ParsedType),    // _Alignas(type-name)
    Expr(ParsedNodeRef), // _Alignas(constant-expression)
}

// Declarators
#[derive(Debug, Clone)]
pub enum ParsedDeclarator {
    Identifier(NameId, TypeQualifiers),                     // Base case: name (e.g., `x`)
    Abstract,                                               // for abstract declarator
    Pointer(TypeQualifiers, Option<Box<ParsedDeclarator>>), // e.g., `*`
    Array(Box<ParsedDeclarator>, ParsedArraySize),          // e.g., `[10]`
    Function {
        inner: Box<ParsedDeclarator>,
        params: ThinVec<ParsedParamData>,
        is_variadic: bool,
    }, // e.g., `(int x)`
    BitField(Box<ParsedDeclarator>, ParsedNodeRef /* bit width expression */), // e.g., `x : 8`
}

impl ParsedDeclarator {}

#[derive(Debug, Clone)]
pub struct ParsedParamData {
    pub specifiers: ThinVec<ParsedDeclSpecifier>,
    pub declarator: Option<ParsedDeclarator>, // Optional name for abstract declarator
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
    VlaSpecifier {
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
pub struct ParsedRecordDefData {
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
impl ParsedDeclSpecifier {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedDeclSpecifier::AlignmentSpecifier(aspec) => aspec.for_each_child(f),
            ParsedDeclSpecifier::TypeSpecifier(ts) => ts.for_each_child(f),
            _ => {}
        }
    }
}

impl ParsedTypeSpecifier {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedTypeSpecifier::Enum(_, Some(enumerators)) => {
                for &e in enumerators {
                    f(e);
                }
            }
            ParsedTypeSpecifier::Record(_, _, Some(def)) => {
                if let Some(members) = &def.members {
                    for &m in members {
                        f(m);
                    }
                }
            }
            ParsedTypeSpecifier::Typeof(_) => {}
            ParsedTypeSpecifier::TypeofExpr(expr) => {
                f(*expr);
            }
            _ => {}
        }
    }
}

impl ParsedAlignmentSpecifier {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        if let ParsedAlignmentSpecifier::Expr(e) = self {
            f(*e)
        }
    }
}

impl ParsedDeclarator {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedDeclarator::Pointer(_, Some(inner)) => {
                inner.for_each_child(f);
            }
            ParsedDeclarator::Pointer(_, None) => {}
            ParsedDeclarator::Array(inner, size) => {
                inner.for_each_child(f);
                size.for_each_child(f);
            }
            ParsedDeclarator::Function { inner, params, .. } => {
                inner.for_each_child(f);
                for p in params {
                    p.for_each_child(f);
                }
            }
            ParsedDeclarator::BitField(inner, size_expr) => {
                inner.for_each_child(f);
                f(*size_expr);
            }
            _ => {}
        }
    }
}

impl ParsedParamData {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        if let Some(decl) = &self.declarator {
            decl.for_each_child(f);
        }
    }
}

impl ParsedArraySize {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedArraySize::Expression { expr, .. } => f(*expr),
            ParsedArraySize::VlaSpecifier { size: Some(s), .. } => f(*s),
            _ => {}
        }
    }
}

impl ParsedInitDeclarator {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        self.declarator.for_each_child(f);
        if let Some(init) = self.initializer {
            f(init);
        }
    }
}

impl ParsedDeclarationData {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        for init in &self.init_declarators {
            init.for_each_child(f);
        }
    }
}

impl ParsedFunctionDefData {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        for spec in &self.specifiers {
            spec.for_each_child(f);
        }
        self.declarator.for_each_child(f);
        f(self.body);
    }
}

impl ParsedNodeKind {
    pub(crate) fn for_each_child(&self, f: &mut impl FnMut(ParsedNodeRef)) {
        match self {
            ParsedNodeKind::Literal(_)
            | ParsedNodeKind::Ident(_)
            | ParsedNodeKind::BuiltinTypesCompatibleP(_, _)
            | ParsedNodeKind::SizeOfType(_)
            | ParsedNodeKind::AlignOf(_)
            | ParsedNodeKind::Break
            | ParsedNodeKind::Continue
            | ParsedNodeKind::Goto(_)
            | ParsedNodeKind::EmptyStatement
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
            | ParsedNodeKind::SizeOfExpr(e)
            | ParsedNodeKind::CompoundLiteral(_, e)
            | ParsedNodeKind::Label(_, e)
            | ParsedNodeKind::Default(e)
            | ParsedNodeKind::GnuStatementExpression(e, _) => f(*e),
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
            ParsedNodeKind::CompoundStatement(stmts) | ParsedNodeKind::TranslationUnit(stmts) => {
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
            ParsedNodeKind::Return(e) | ParsedNodeKind::ExpressionStatement(e) => {
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
