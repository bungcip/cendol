use std::fmt::Display;

use crate::SourceSpan;
use crate::parser::string_interner::StringId;
use crate::types::{TypeId, TypeKind, TypeSpec, TypeSpecKind, TypeQualifiers, StorageClass, TypeKeywordMask};
use thin_vec::ThinVec;

/// Type alias for initializer lists.
pub type InitializerList = ThinVec<(ThinVec<Designator>, Box<Initializer>)>;

impl TypeSpec {
    pub fn span(&self) -> SourceSpan {
        SourceSpan::default()
    }
}

/// Field in struct/union
#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
    pub name: Option<StringId>,
    pub type_spec: TypeSpec,
    pub span: SourceSpan,
}

/// Struct declaration node
#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub name: Option<StringId>,       // None = anonymous
    pub fields: Vec<StructField>,     // empty if forward declaration
    pub span: SourceSpan,
}

/// Enum member
#[derive(Debug, Clone, PartialEq)]
pub struct EnumMember {
    pub name: StringId,
    pub value: Option<Box<Expr>>,
    pub span: SourceSpan,
}

/// Enum declaration
#[derive(Debug, Clone, PartialEq)]
pub struct EnumDecl {
    pub name: Option<StringId>,
    pub members: Vec<EnumMember>,
    pub span: SourceSpan,
}

/// Variable declaration
#[derive(Debug, Clone, PartialEq)]
pub struct VarDecl {
    pub name: StringId,
    pub type_spec: TypeSpec,
    pub init: Option<Initializer>,
    pub span: SourceSpan,
}

/// Function declaration
#[derive(Debug, Clone, PartialEq)]
pub struct FuncDecl {
    pub name: StringId,
    pub return_type: TypeSpec,
    pub params: ThinVec<VarDecl>,
    pub body: Option<ThinVec<Stmt>>, // None if only prototype
    pub is_variadic: bool,
    pub is_inline: bool,
    pub is_noreturn: bool,
    pub span: SourceSpan,
}

/// Declaration enum that encompasses all types of declarations
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Var(VarDecl),
    Func(FuncDecl),
    Struct(StructDecl),
    Union(StructDecl),
    Enum(EnumDecl),
    Typedef(StringId, TypeSpec),
    StaticAssert(Box<Expr>, StringId),
}

/// Converts a TypeSpec to a TypeId by building the corresponding TypeKind and interning it.
pub fn type_spec_to_type_id(type_spec: &TypeSpec, span: SourceSpan) -> TypeId {
    let mut kind = match &type_spec.kind {
        TypeSpecKind::Builtin(mask) => {
            if *mask == 0 {
                TypeKind::Int
            } else {
                // Determine the primary type based on the mask
                if *mask & TypeKeywordMask::VOID.bits() != 0 {
                    TypeKind::Void
                } else if *mask & TypeKeywordMask::BOOL.bits() != 0 {
                    TypeKind::Bool
                } else if *mask & TypeKeywordMask::CHAR.bits() != 0 {
                    if *mask & TypeKeywordMask::UNSIGNED.bits() != 0 {
                        TypeKind::UnsignedChar
                    } else {
                        TypeKind::Char
                    }
                } else if *mask & TypeKeywordMask::SHORT.bits() != 0 {
                    if *mask & TypeKeywordMask::UNSIGNED.bits() != 0 {
                        TypeKind::UnsignedShort
                    } else {
                        TypeKind::Short
                    }
                } else if *mask & TypeKeywordMask::INT.bits() != 0 {
                    if *mask & TypeKeywordMask::UNSIGNED.bits() != 0 {
                        TypeKind::UnsignedInt
                    } else {
                        TypeKind::Int
                    }
                } else if *mask & TypeKeywordMask::LONG.bits() != 0 {
                    if *mask & TypeKeywordMask::LONGLONG.bits() != 0 {
                        if *mask & TypeKeywordMask::UNSIGNED.bits() != 0 {
                            TypeKind::UnsignedLongLong
                        } else {
                            TypeKind::LongLong
                        }
                    } else {
                        if *mask & TypeKeywordMask::UNSIGNED.bits() != 0 {
                            TypeKind::UnsignedLong
                        } else {
                            TypeKind::Long
                        }
                    }
                } else if *mask & TypeKeywordMask::FLOAT.bits() != 0 {
                    TypeKind::Float
                } else if *mask & TypeKeywordMask::DOUBLE.bits() != 0 {
                    TypeKind::Double
                } else {
                    TypeKind::Int // Default fallback
                }
            }
        }
        TypeSpecKind::Struct(name_id) => {
            // For struct types in TypeSpec, we don't have field information
            // Field information is handled separately via Decl::Struct
            TypeKind::Struct(Some(*name_id), thin_vec::ThinVec::new())
        },
        TypeSpecKind::Union(name_id) => {
            // For union types in TypeSpec, we don't have field information
            // Field information is handled separately via Decl::Union
            TypeKind::Union(Some(*name_id), thin_vec::ThinVec::new())
        },
        TypeSpecKind::Enum(name_id) => TypeKind::Enum {
            name: Some(*name_id),
            underlying_type: TypeId::INT,
            variants: thin_vec::ThinVec::new(),
        },
        TypeSpecKind::Typedef(_name_id) => TypeKind::Int, // Fallback for typedef
    };

    // Apply array sizes
    for array_size in &type_spec.array_sizes {
        if let Expr::Number(size, _) = array_size {
            if *size > 0 {
                kind = TypeKind::Array(TypeId::intern(&kind), *size as usize);
            } else {
                kind = TypeKind::Array(TypeId::intern(&kind), 0);
            }
        }
    }

    // Apply pointers
    for _ in 0..type_spec.pointer_depth {
        kind = TypeKind::Pointer(TypeId::intern(&kind));
    }

    // Apply qualifiers
    let mut flags = kind.flags();
    if type_spec.qualifiers.contains(TypeQualifiers::CONST) {
        flags |= TypeId::FLAG_CONST;
    }
    if type_spec.qualifiers.contains(TypeQualifiers::VOLATILE) {
        flags |= TypeId::FLAG_VOLATILE;
    }
    if type_spec.qualifiers.contains(TypeQualifiers::RESTRICT) {
        flags |= TypeId::FLAG_RESTRICT;
    }
    if type_spec.qualifiers.contains(TypeQualifiers::ATOMIC) {
        flags |= TypeId::FLAG_ATOMIC;
    }

    TypeId::intern_with_flags(&kind, flags)
}

/// Represents the initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum ForInit {
    /// A variable declaration.
    Declaration(TypeSpec, StringId, Option<Initializer>),
    /// An expression.
    Expr(Expr),
}

/// Represents a declarator, which includes the type modifiers (pointers, arrays) and the identifier.
#[derive(Debug, PartialEq, Clone)]
pub struct Declarator {
    pub ty: TypeSpec,
    pub name: StringId,
    pub initializer: Option<Initializer>,
    pub span: SourceSpan,
}

/// Represents a statement in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    /// A `return` statement.
    Return(Box<Expr>),
    /// An `if` statement.
    If(Box<Expr>, Box<Stmt>, Option<Box<Stmt>>),
    /// A `while` loop.
    While(Box<Expr>, Box<Stmt>),
    /// A `for` loop.
    For(
        Option<Box<ForInit>>,
        Option<Box<Expr>>,
        Option<Box<Expr>>,
        Box<Stmt>,
    ),
    /// A block of statements.
    Block(ThinVec<Stmt>),
    /// A `switch` statement.
    Switch(Box<Expr>, Box<Stmt>),
    /// A `case` statement.
    Case(Box<Expr>, Box<Stmt>),
    /// A `default` statement in a `switch`.
    Default(Box<Stmt>),
    /// A labeled statement.
    Label(StringId, Box<Stmt>, SourceSpan),
    /// A `goto` statement.
    Goto(StringId, SourceSpan),
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<Stmt>, Box<Expr>),
    /// An empty statement.
    Empty,
    /// An expression statement.
    Expr(Box<Expr>),
    /// A declaration statement.
    Declaration(TypeSpec, ThinVec<Declarator>, bool),
    /// A static assert statement.
    StaticAssert(Box<Expr>, StringId),
}

impl Stmt {
    pub fn span(&self) -> SourceSpan {
        match self {
            Stmt::Return(expr) => expr.span(),
            Stmt::If(cond, _, _) => cond.span(),
            Stmt::While(cond, _) => cond.span(),
            Stmt::For(init, _, _, _) => {
                if let Some(init) = init {
                    match &**init {
                        ForInit::Declaration(_, _, initializer) => {
                            if let Some(initializer) = initializer {
                                match initializer {
                                    Initializer::Expr(expr) => expr.span(),
                                    Initializer::List(_) => SourceSpan::default(),
                                }
                            } else {
                                SourceSpan::default()
                            }
                        }
                        ForInit::Expr(expr) => expr.span(),
                    }
                } else {
                    SourceSpan::default()
                }
            }
            Stmt::Block(stmts) => stmts.first().map_or(SourceSpan::default(), |s| s.span()),
            Stmt::Switch(expr, _) => expr.span(),
            Stmt::Case(expr, _) => expr.span(),
            Stmt::Default(body) => body.span(),
            Stmt::Label(_, _, span) => *span,
            Stmt::Goto(_, span) => *span,
            Stmt::Break => SourceSpan::default(),
            Stmt::Continue => SourceSpan::default(),
            Stmt::DoWhile(body, _) => body.span(),
            Stmt::Empty => SourceSpan::default(),
            Stmt::Expr(expr) => expr.span(),
            Stmt::Declaration(_, _, _) => SourceSpan::default(),
            Stmt::StaticAssert(_, _) => SourceSpan::default(),
        }
    }
}

/// Represents an expression in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    Comma,
}

/// Represents assignment operators.
#[derive(Debug, PartialEq, Clone)]
pub enum AssignOp {
    Assign,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseXor,
    BitwiseOr,
}

/// Represents logical operators.
#[derive(Debug, PartialEq, Clone)]
pub enum LogicalOp {
    And,
    Or,
}

impl LogicalOp {
    /// Converts a LogicalOp to the corresponding BinOp.
    pub fn to_binop(&self) -> BinOp {
        match self {
            LogicalOp::And => BinOp::LogicalAnd,
            LogicalOp::Or => BinOp::LogicalOr,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// A number literal.
    Number(i64, SourceSpan),
    /// A float number literal.
    FloatNumber(f64, SourceSpan),
    /// A string literal.
    String(StringId, SourceSpan),
    /// A character literal.
    Char(StringId, SourceSpan),
    /// A variable.
    Variable(StringId, SourceSpan),
    /// An assignment expression.
    Assign(Box<Expr>, Box<Expr>),
    /// A compound assignment expression (e.g., +=, -=, *=, /=, %=).
    AssignAdd(Box<Expr>, Box<Expr>),
    AssignSub(Box<Expr>, Box<Expr>),
    AssignMul(Box<Expr>, Box<Expr>),
    AssignDiv(Box<Expr>, Box<Expr>),
    AssignMod(Box<Expr>, Box<Expr>),
    AssignLeftShift(Box<Expr>, Box<Expr>),
    AssignRightShift(Box<Expr>, Box<Expr>),
    AssignBitwiseAnd(Box<Expr>, Box<Expr>),
    AssignBitwiseXor(Box<Expr>, Box<Expr>),
    AssignBitwiseOr(Box<Expr>, Box<Expr>),
    /// An addition expression.
    Add(Box<Expr>, Box<Expr>),
    /// A subtraction expression.
    Sub(Box<Expr>, Box<Expr>),
    /// A multiplication expression.
    Mul(Box<Expr>, Box<Expr>),
    /// A division expression.
    Div(Box<Expr>, Box<Expr>),
    /// A modulo expression.
    Mod(Box<Expr>, Box<Expr>),
    /// An equality comparison.
    Equal(Box<Expr>, Box<Expr>),
    /// An inequality comparison.
    NotEqual(Box<Expr>, Box<Expr>),
    /// A less-than comparison.
    LessThan(Box<Expr>, Box<Expr>),
    /// A greater-than comparison.
    GreaterThan(Box<Expr>, Box<Expr>),
    /// A less-than-or-equal-to comparison.
    LessThanOrEqual(Box<Expr>, Box<Expr>),
    /// A greater-than-or-equal-to comparison.
    GreaterThanOrEqual(Box<Expr>, Box<Expr>),
    /// A left shift expression.
    LeftShift(Box<Expr>, Box<Expr>),
    /// A right shift expression.
    RightShift(Box<Expr>, Box<Expr>),
    /// A function call.
    Call(StringId, ThinVec<Expr>, SourceSpan),
    /// A logical AND expression.
    LogicalAnd(Box<Expr>, Box<Expr>),
    /// A logical OR expression.
    LogicalOr(Box<Expr>, Box<Expr>),
    /// A bitwise OR expression.
    BitwiseOr(Box<Expr>, Box<Expr>),
    /// A bitwise XOR expression.
    BitwiseXor(Box<Expr>, Box<Expr>),
    /// A bitwise AND expression.
    BitwiseAnd(Box<Expr>, Box<Expr>),
    /// A logical NOT expression.
    LogicalNot(Box<Expr>),
    /// A dereference expression.
    Deref(Box<Expr>),
    /// An address-of expression.
    AddressOf(Box<Expr>),
    /// A negation expression.
    Neg(Box<Expr>),
    /// A bitwise NOT expression.
    BitwiseNot(Box<Expr>),
    /// A sizeof expression.
    Sizeof(Box<Expr>),
    /// A sizeof type expression.
    SizeofType(TypeSpec),
    /// An alignof expression.
    Alignof(Box<Expr>),
    /// An alignof type expression.
    AlignofType(TypeSpec),
    /// A pre-increment expression.
    PreIncrement(Box<Expr>),
    /// A pre-decrement expression.
    PreDecrement(Box<Expr>),
    /// A post-increment expression.
    PostIncrement(Box<Expr>),
    /// A post-decrement expression.
    PostDecrement(Box<Expr>),
    /// A ternary conditional expression.
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// An initializer list expression.
    InitializerList(InitializerList),
    /// A member access expression.
    Member(Box<Expr>, StringId),
    /// A pointer member access expression.
    PointerMember(Box<Expr>, StringId),
    /// An explicit type cast expression.
    ExplicitCast(Box<TypeSpec>, Box<Expr>),
    /// An implicit type cast expression.
    ImplicitCast(Box<TypeSpec>, Box<Expr>),
    /// A compound literal expression.
    CompoundLiteral(Box<TypeSpec>, Box<Initializer>),
    /// A _Generic expression.
    Generic(Box<Expr>, Vec<(Option<TypeSpec>, Box<Expr>)>),
    /// A comma expression.
    Comma(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn get_logical_expr(&self) -> Option<(LogicalOp, &Expr, &Expr)> {
        match self {
            Expr::LogicalAnd(lhs, rhs) => Some((LogicalOp::And, lhs, rhs)),
            Expr::LogicalOr(lhs, rhs) => Some((LogicalOp::Or, lhs, rhs)),
            _ => None,
        }
    }

    pub fn get_binary_expr(&self) -> Option<(BinOp, &Expr, &Expr)> {
        if let Some((logical_op, lhs, rhs)) = self.get_logical_expr() {
            Some((logical_op.to_binop(), lhs, rhs))
        } else {
            match self {
                Expr::Add(lhs, rhs) => Some((BinOp::Add, lhs, rhs)),
                Expr::Sub(lhs, rhs) => Some((BinOp::Sub, lhs, rhs)),
                Expr::Mul(lhs, rhs) => Some((BinOp::Mul, lhs, rhs)),
                Expr::Div(lhs, rhs) => Some((BinOp::Div, lhs, rhs)),
                Expr::Mod(lhs, rhs) => Some((BinOp::Mod, lhs, rhs)),
                Expr::Equal(lhs, rhs) => Some((BinOp::Equal, lhs, rhs)),
                Expr::NotEqual(lhs, rhs) => Some((BinOp::NotEqual, lhs, rhs)),
                Expr::LessThan(lhs, rhs) => Some((BinOp::LessThan, lhs, rhs)),
                Expr::GreaterThan(lhs, rhs) => Some((BinOp::GreaterThan, lhs, rhs)),
                Expr::LessThanOrEqual(lhs, rhs) => Some((BinOp::LessThanOrEqual, lhs, rhs)),
                Expr::GreaterThanOrEqual(lhs, rhs) => Some((BinOp::GreaterThanOrEqual, lhs, rhs)),
                Expr::LeftShift(lhs, rhs) => Some((BinOp::LeftShift, lhs, rhs)),
                Expr::RightShift(lhs, rhs) => Some((BinOp::RightShift, lhs, rhs)),
                Expr::BitwiseOr(lhs, rhs) => Some((BinOp::BitwiseOr, lhs, rhs)),
                Expr::BitwiseXor(lhs, rhs) => Some((BinOp::BitwiseXor, lhs, rhs)),
                Expr::BitwiseAnd(lhs, rhs) => Some((BinOp::BitwiseAnd, lhs, rhs)),
                Expr::Comma(lhs, rhs) => Some((BinOp::Comma, lhs, rhs)),
                _ => None,
            }
        }
    }

    pub fn get_assign_expr(&self) -> Option<(AssignOp, &Expr, &Expr)> {
        match self {
            Expr::Assign(lhs, rhs) => Some((AssignOp::Assign, lhs, rhs)),
            Expr::AssignAdd(lhs, rhs) => Some((AssignOp::Add, lhs, rhs)),
            Expr::AssignSub(lhs, rhs) => Some((AssignOp::Sub, lhs, rhs)),
            Expr::AssignMul(lhs, rhs) => Some((AssignOp::Mul, lhs, rhs)),
            Expr::AssignDiv(lhs, rhs) => Some((AssignOp::Div, lhs, rhs)),
            Expr::AssignMod(lhs, rhs) => Some((AssignOp::Mod, lhs, rhs)),
            Expr::AssignLeftShift(lhs, rhs) => Some((AssignOp::LeftShift, lhs, rhs)),
            Expr::AssignRightShift(lhs, rhs) => Some((AssignOp::RightShift, lhs, rhs)),
            Expr::AssignBitwiseAnd(lhs, rhs) => Some((AssignOp::BitwiseAnd, lhs, rhs)),
            Expr::AssignBitwiseXor(lhs, rhs) => Some((AssignOp::BitwiseXor, lhs, rhs)),
            Expr::AssignBitwiseOr(lhs, rhs) => Some((AssignOp::BitwiseOr, lhs, rhs)),
            _ => None,
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            Expr::Variable(_, span) => *span,
            Expr::Call(_, _, span) => *span,
            Expr::Assign(lhs, _)
            | Expr::AssignAdd(lhs, _)
            | Expr::AssignSub(lhs, _)
            | Expr::AssignMul(lhs, _)
            | Expr::AssignDiv(lhs, _)
            | Expr::AssignMod(lhs, _)
            | Expr::AssignLeftShift(lhs, _)
            | Expr::AssignRightShift(lhs, _)
            | Expr::AssignBitwiseAnd(lhs, _)
            | Expr::AssignBitwiseXor(lhs, _)
            | Expr::AssignBitwiseOr(lhs, _)
            | Expr::Add(lhs, _)
            | Expr::Sub(lhs, _)
            | Expr::Mul(lhs, _)
            | Expr::Div(lhs, _)
            | Expr::Mod(lhs, _)
            | Expr::Equal(lhs, _)
            | Expr::NotEqual(lhs, _)
            | Expr::LessThan(lhs, _)
            | Expr::GreaterThan(lhs, _)
            | Expr::LessThanOrEqual(lhs, _)
            | Expr::GreaterThanOrEqual(lhs, _)
            | Expr::LeftShift(lhs, _)
            | Expr::RightShift(lhs, _)
            | Expr::LogicalAnd(lhs, _)
            | Expr::LogicalOr(lhs, _)
            | Expr::BitwiseOr(lhs, _)
            | Expr::BitwiseXor(lhs, _)
            | Expr::BitwiseAnd(lhs, _)
            | Expr::Comma(lhs, _) => lhs.span(),
            Expr::LogicalNot(expr)
            | Expr::Deref(expr)
            | Expr::AddressOf(expr)
            | Expr::Neg(expr)
            | Expr::BitwiseNot(expr)
            | Expr::Sizeof(expr)
            | Expr::Alignof(expr)
            | Expr::PreIncrement(expr)
            | Expr::PreDecrement(expr)
            | Expr::PostIncrement(expr)
            | Expr::PostDecrement(expr) => expr.span(),
            Expr::Ternary(cond, _, _) => cond.span(),
            Expr::Member(expr, _) | Expr::PointerMember(expr, _) => expr.span(),
            Expr::ExplicitCast(_, expr) | Expr::ImplicitCast(_, expr) => expr.span(),
            // For literals and other complex types, a default span is returned for now.
            // A more robust solution would involve storing spans in all Expr variants.
            _ => SourceSpan::default(),
        }
    }
}

/// Represents a C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum Designator {
    /// An array designator, e.g., `[0]`.
    Index(Box<Expr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(StringId),
}

/// Represents a C initializer.
#[derive(Debug, PartialEq, Clone)]
pub enum Initializer {
    /// A single expression initializer.
    Expr(Box<Expr>),
    /// An initializer list, e.g., `{ [0] = 1, .x = 2 }`.
    List(InitializerList),
}

/// Represents a function parameter.
#[derive(Debug, PartialEq, Clone)]
pub struct Parameter {
    /// The type of the parameter.
    pub ty: TypeSpec,
    /// The name of the parameter.
    pub name: StringId,
    /// The span of the parameter.
    pub span: SourceSpan,
}

/// Represents a program.
#[derive(Debug, PartialEq, Clone)]
pub struct TranslationUnit {
    /// The global declarations and function definitions.
    pub globals: ThinVec<Decl>,
}
