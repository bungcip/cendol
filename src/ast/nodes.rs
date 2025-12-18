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
    GnuStatementExpression(
        NodeRef, /* compound statement */
        NodeRef, /* result expression */
    ),

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
    pub initializer: Initializer,
}

#[derive(Debug, Clone, Serialize)]
pub enum Designator {
    FieldName(Symbol),
    ArrayIndex(NodeRef),             // Index expression
    GnuArrayRange(NodeRef, NodeRef), // GCC extension: Range expression [start ... end]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Ast, Node};
    use crate::source_manager::SourceSpan;

    #[test]
    fn test_literal_int_constructor() {
        let node = NodeKind::literal_int(42);
        assert!(matches!(node, NodeKind::LiteralInt(42)));
    }

    #[test]
    fn test_literal_float_constructor() {
        let node = NodeKind::literal_float(3.14);
        assert!(matches!(node, NodeKind::LiteralFloat(3.14)));
    }

    #[test]
    fn test_literal_string_constructor() {
        let symbol: Symbol = "hello".into();
        let node = NodeKind::literal_string(symbol);
        assert!(matches!(node, NodeKind::LiteralString(s) if s == symbol));
    }

    #[test]
    fn test_literal_char_constructor() {
        let node = NodeKind::literal_char(b'a');
        assert!(matches!(node, NodeKind::LiteralChar(b'a')));
    }

    #[test]
    fn test_ident_constructor() {
        let symbol: Symbol = "x".into();
        let node = NodeKind::ident(symbol);
        assert!(matches!(node, NodeKind::Ident(s, _) if s == symbol));
    }

    #[test]
    fn test_binary_op_constructor() {
        let mut ast = Ast::new();
        let left = ast.push_node(Node::new(NodeKind::LiteralInt(1), SourceSpan::empty()));
        let right = ast.push_node(Node::new(NodeKind::LiteralInt(2), SourceSpan::empty()));
        let node = NodeKind::binary_op(BinaryOp::Add, left, right);
        assert!(matches!(node, NodeKind::BinaryOp(BinaryOp::Add, l, r) if l == left && r == right));
    }

    #[test]
    fn test_function_call_constructor() {
        let mut ast = Ast::new();
        let func = ast.push_node(Node::new(NodeKind::ident("my_func".into()), SourceSpan::empty()));
        let arg = ast.push_node(Node::new(NodeKind::LiteralInt(42), SourceSpan::empty()));
        let node = NodeKind::function_call(func, vec![arg]);
        assert!(matches!(node, NodeKind::FunctionCall(f, args) if f == func && args[0] == arg));
    }

    #[test]
    fn test_if_stmt_builder_success() {
        let mut ast = Ast::new();
        let cond = ast.push_node(Node::new(NodeKind::LiteralInt(1), SourceSpan::empty()));
        let then = ast.push_node(Node::new(NodeKind::EmptyStatement, SourceSpan::empty()));
        let if_stmt = IfStmtBuilder::new().condition(cond).then_branch(then).build().unwrap();
        assert_eq!(if_stmt.condition, cond);
        assert_eq!(if_stmt.then_branch, then);
        assert!(if_stmt.else_branch.is_none());
    }

    #[test]
    fn test_if_stmt_builder_missing_condition() {
        let mut ast = Ast::new();
        let then = ast.push_node(Node::new(NodeKind::EmptyStatement, SourceSpan::empty()));
        let result = IfStmtBuilder::new().then_branch(then).build();
        assert!(result.is_err());
    }

    #[test]
    fn test_declaration_data_builder() {
        let builder = DeclarationDataBuilder::new();
        let specifier = DeclSpecifier::TypeSpecifier(TypeSpecifier::Int);
        let init_declarator = InitDeclarator {
            declarator: Declarator::Identifier("x".into(), Default::default(), None),
            initializer: None,
        };
        let decl_data = builder
            .add_specifier(specifier.clone())
            .add_init_declarator(init_declarator.clone())
            .build();

        assert_eq!(decl_data.specifiers.len(), 1);
        assert_eq!(decl_data.init_declarators.len(), 1);
        assert!(matches!(
            &decl_data.specifiers[0],
            DeclSpecifier::TypeSpecifier(TypeSpecifier::Int)
        ));
        assert!(
            matches!(&decl_data.init_declarators[0].declarator, Declarator::Identifier(s, _, None) if s == &"x".into())
        );
    }
}
