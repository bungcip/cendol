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
    AtomicOp(AtomicOp, Vec<ParsedNodeRef>),
    SizeOfExpr(ParsedNodeRef),
    SizeOfType(ParsedType),
    AlignOf(ParsedType),

    CompoundLiteral(ParsedType, ParsedNodeRef),
    GenericSelection(ParsedNodeRef, Vec<ParsedGenericAssociation>),

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
        has_proto: bool,
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
