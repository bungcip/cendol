//! AST Node definitions, constructors, and builder patterns.
//!
//! This module contains the core AST node types, including the NodeKind enum
//! and associated data structures. It provides constructors and builder patterns
//! for creating complex AST nodes ergonomically.

use serde::Serialize;
use std::cell::Cell;
use thin_vec::ThinVec;

use crate::ast::{InitializerRef, NodeRef, Symbol, SymbolEntryRef, TypeRef};

/// The core enum defining all possible AST node types for C11.
/// Variants use NodeIndex for child references, enabling flattened storage.
/// Maintained original structure for compatibility, but moved to this module.
#[derive(Debug, Clone, Serialize)]
pub enum NodeKind {
    // --- Literals (Inline storage for common types) ---
    LiteralInt(i64), // Parsed integer literal value
    LiteralFloat(f64),
    LiteralString(Symbol),
    LiteralChar(u8),

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
    EnumConstant(Symbol, Option<NodeRef> /* value expr */),
    StaticAssert(NodeRef /* condition */, Symbol /* message */),

    // --- Top Level ---
    TranslationUnit(Vec<NodeRef> /* top-level declarations */),

    // --- Dummy Node ---
    Dummy,
}

// Structs for Large/Indirect Variants (to keep NodeKind size small and cache-friendly)
// These are stored separately with index-based references.

// Control flow statements
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

// Declaration data
#[derive(Debug, Clone, Serialize)]
pub struct DeclarationData {
    pub specifiers: ThinVec<DeclSpecifier>,
    pub init_declarators: ThinVec<InitDeclarator>,
}

#[derive(Debug, Clone, Serialize)]
pub struct InitDeclarator {
    pub declarator: Declarator,
    pub initializer: Option<Initializer>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionDefData {
    pub specifiers: ThinVec<DeclSpecifier>,
    pub declarator: Declarator,
    pub body: NodeRef, // A CompoundStatement
}

// Declaration specifiers and related types
#[derive(Debug, Clone, Serialize)]
pub struct DeclSpecifier {
    pub storage_class: Option<StorageClass>,
    pub type_qualifiers: TypeQualifiers,
    pub function_specifiers: FunctionSpecifiers,
    pub alignment_specifier: Option<AlignmentSpecifier>,
    pub type_specifier: TypeSpecifier,
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
        Option<Symbol>,        /* tag */
        Option<RecordDefData>, /* definition */
    ),
    Enum(
        Option<Symbol>,       /* tag */
        Option<Vec<NodeRef>>, /* enumerators */
    ),
    TypedefName(Symbol),
}

// Storage classes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
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
    Identifier(Symbol, TypeQualifiers, Option<Box<Declarator>>), // Base case: name (e.g., `x`)
    Abstract,                                                    // for abstract declarator
    Pointer(TypeQualifiers, Option<Box<Declarator>>),            // e.g., `*`
    Array(Box<Declarator>, ArraySize),                           // e.g., `[10]`
    Function(Box<Declarator>, ThinVec<ParamData> /* parameters */), // e.g., `(int x)`
    AnonymousRecord(bool /* is_union */, ThinVec<DeclarationData> /* members */), // C11 anonymous struct/union
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
    pub tag: Option<Symbol>,                   // None if anonymous
    pub members: Option<Vec<DeclarationData>>, // Field declarations
    pub is_union: bool,
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
    pub initializer: Initializer,
}

#[derive(Debug, Clone, Serialize)]
pub enum Designator {
    FieldName(Symbol),
    ArrayIndex(NodeRef), // Index expression
}

// Generic selection
#[derive(Debug, Clone, Serialize)]
pub struct GenericAssociation {
    pub type_name: Option<TypeRef>, // None for 'default:'
    pub result_expr: NodeRef,
}

// --- Builder Patterns ---

/// Builder for IfStmt
#[derive(Debug)]
pub struct IfStmtBuilder {
    condition: Option<NodeRef>,
    then_branch: Option<NodeRef>,
    else_branch: Option<NodeRef>,
}

impl Default for IfStmtBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl IfStmtBuilder {
    pub fn new() -> Self {
        IfStmtBuilder {
            condition: None,
            then_branch: None,
            else_branch: None,
        }
    }

    pub fn condition(mut self, condition: NodeRef) -> Self {
        self.condition = Some(condition);
        self
    }

    pub fn then_branch(mut self, then_branch: NodeRef) -> Self {
        self.then_branch = Some(then_branch);
        self
    }

    pub fn else_branch(mut self, else_branch: Option<NodeRef>) -> Self {
        self.else_branch = else_branch;
        self
    }

    pub fn build(self) -> Result<IfStmt, &'static str> {
        Ok(IfStmt {
            condition: self.condition.ok_or("condition is required")?,
            then_branch: self.then_branch.ok_or("then_branch is required")?,
            else_branch: self.else_branch,
        })
    }
}

/// Builder for DeclarationData
#[derive(Debug)]
pub struct DeclarationDataBuilder {
    specifiers: ThinVec<DeclSpecifier>,
    init_declarators: ThinVec<InitDeclarator>,
}

impl Default for DeclarationDataBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl DeclarationDataBuilder {
    pub fn new() -> Self {
        DeclarationDataBuilder {
            specifiers: ThinVec::new(),
            init_declarators: ThinVec::new(),
        }
    }

    pub fn add_specifier(mut self, specifier: DeclSpecifier) -> Self {
        self.specifiers.push(specifier);
        self
    }

    pub fn add_init_declarator(mut self, init_declarator: InitDeclarator) -> Self {
        self.init_declarators.push(init_declarator);
        self
    }

    pub fn build(self) -> DeclarationData {
        DeclarationData {
            specifiers: self.specifiers,
            init_declarators: self.init_declarators,
        }
    }
}

// Add more builders as needed...

// --- Convenience Constructors ---

impl NodeKind {
    /// Create a literal integer node
    pub fn literal_int(value: i64) -> Self {
        NodeKind::LiteralInt(value)
    }

    /// Create a literal float node
    pub fn literal_float(value: f64) -> Self {
        NodeKind::LiteralFloat(value)
    }

    /// Create a literal string node
    pub fn literal_string(value: Symbol) -> Self {
        NodeKind::LiteralString(value)
    }

    /// Create a literal char node
    pub fn literal_char(value: u8) -> Self {
        NodeKind::LiteralChar(value)
    }

    /// Create an identifier node
    pub fn ident(name: Symbol) -> Self {
        NodeKind::Ident(name, Cell::new(None))
    }

    /// Create a binary operation node
    pub fn binary_op(op: BinaryOp, left: NodeRef, right: NodeRef) -> Self {
        NodeKind::BinaryOp(op, left, right)
    }

    /// Create a function call node
    pub fn function_call(func: NodeRef, args: Vec<NodeRef>) -> Self {
        NodeKind::FunctionCall(func, args)
    }

    // Add more constructors as needed...
}
