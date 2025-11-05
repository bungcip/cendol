use crate::SourceSpan;
use crate::parser::ast::{BinOp, AssignOp};
use crate::parser::string_interner::StringId;
use crate::types::TypeId;
use thin_vec::ThinVec;

/// Type alias for typed initializer lists.
pub type TypedInitializerList = ThinVec<(ThinVec<TypedDesignator>, Box<TypedInitializer>)>;

/// Represents a typed function parameter (for semantic analysis).
#[derive(Debug, PartialEq, Clone)]
pub struct TypedParameter {
    /// The resolved type of the parameter.
    pub ty: TypeId,
    /// The name of the parameter.
    pub name: StringId,
    /// The span of the parameter.
    pub span: SourceSpan,
}

impl TypedParameter {
    pub fn from_parameter(param: crate::parser::ast::Parameter) -> Self {
        let ty = crate::parser::ast::type_spec_to_type_id(&param.ty, SourceSpan::default());
        Self {
            ty: ty,
            name: param.name,
            span: param.span,
        }
    }
}

/// Represents a typed expression with type information.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedExpr {
    Number(i64, SourceSpan, TypeId),
    FloatNumber(f64, SourceSpan, TypeId),
    String(StringId, SourceSpan, TypeId),
    Char(StringId, SourceSpan, TypeId),
    Variable(StringId, SourceSpan, TypeId),
    Call(StringId, ThinVec<TypedExpr>, SourceSpan, TypeId),
    Assign(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignAdd(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignSub(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignMul(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignDiv(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignMod(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignLeftShift(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignRightShift(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignBitwiseAnd(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignBitwiseXor(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    AssignBitwiseOr(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, TypeId),
    Add(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Sub(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Mul(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Div(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Mod(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Equal(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    NotEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    LessThan(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    GreaterThan(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    LessThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    GreaterThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    LogicalAnd(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    LogicalOr(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    BitwiseOr(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    BitwiseXor(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    BitwiseAnd(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    LeftShift(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    RightShift(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Comma(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, TypeId),
    Neg(Box<TypedExpr>, SourceSpan, TypeId),
    LogicalNot(Box<TypedExpr>, SourceSpan, TypeId),
    BitwiseNot(Box<TypedExpr>, SourceSpan, TypeId),
    Sizeof(Box<TypedExpr>, SourceSpan, TypeId),
    Deref(Box<TypedExpr>, SourceSpan, TypeId),
    AddressOf(Box<TypedLValue>, SourceSpan, TypeId),
    SizeofType(TypeId, SourceSpan, TypeId),
    Alignof(Box<TypedExpr>, SourceSpan, TypeId),
    AlignofType(TypeId, SourceSpan, TypeId),
    Ternary(
        Box<TypedExpr>,
        Box<TypedExpr>,
        Box<TypedExpr>,
        SourceSpan,
        TypeId,
    ),
    Member(Box<TypedExpr>, StringId, SourceSpan, TypeId),
    PointerMember(Box<TypedExpr>, StringId, SourceSpan, TypeId),
    InitializerList(TypedInitializerList, SourceSpan, TypeId),
    ExplicitCast(TypeId, Box<TypedExpr>, SourceSpan, TypeId),
    ImplicitCast(TypeId, Box<TypedExpr>, SourceSpan, TypeId),
    CompoundLiteral(TypeId, Box<TypedInitializer>, SourceSpan, TypeId),
    PreIncrement(Box<TypedLValue>, SourceSpan, TypeId),
    PreDecrement(Box<TypedLValue>, SourceSpan, TypeId),
    PostIncrement(Box<TypedLValue>, SourceSpan, TypeId),
    PostDecrement(Box<TypedLValue>, SourceSpan, TypeId),
}

/// Represents a typed LValue expression with type information.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedLValue {
    /// A variable identifier.
    Variable(StringId, SourceSpan, TypeId),
    /// A dereference of a pointer expression.
    Deref(Box<TypedExpr>, SourceSpan, TypeId),
    /// A member access of a struct/union expression.
    Member(Box<TypedExpr>, StringId, SourceSpan, TypeId),
    /// A string literal.
    String(StringId, SourceSpan, TypeId),
}

impl TypedLValue {
    pub fn ty(&self) -> TypeId {
        match self {
            TypedLValue::Variable(_, _, ty) => *ty,
            TypedLValue::Deref(_, _, ty) => *ty,
            TypedLValue::Member(_, _, _, ty) => *ty,
            TypedLValue::String(_, _, ty) => *ty,
        }
    }

    pub fn is_modifiable(&self) -> bool {
        matches!(self, TypedLValue::String(_, _, _)) == false
    }
}

/// Represents a typed C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedDesignator {
    /// An array designator, e.g., `[0]`.
    Index(Box<TypedExpr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(StringId),
}

/// Represents a typed C initializer.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedInitializer {
    /// A single expression initializer.
    Expr(Box<TypedExpr>),
    /// An initializer list, e.g., `{ [0] = 1, .x = 2 }`.
    List(TypedInitializerList),
}

/// Represents a typed declarator, which includes the type modifiers (pointers, arrays) and the identifier.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedDeclarator {
    pub ty: TypeId,
    pub name: StringId,
    pub initializer: Option<TypedInitializer>,
}

/// Represents the typed initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedForInit {
    /// A variable declaration.
    Declaration(TypeId, StringId, Option<TypedInitializer>),
    /// An expression.
    Expr(TypedExpr),
}

/// Represents a typed statement with type information where applicable.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedStmt {
    /// A `return` statement.
    Return(TypedExpr),
    /// An `if` statement.
    If(TypedExpr, Box<TypedStmt>, Option<Box<TypedStmt>>),
    /// A `while` loop.
    While(TypedExpr, Box<TypedStmt>),
    /// A `for` loop.
    For(
        Box<Option<TypedForInit>>,
        Box<Option<TypedExpr>>,
        Box<Option<TypedExpr>>,
        Box<TypedStmt>,
    ),
    /// A block of statements.
    Block(ThinVec<TypedStmt>),
    /// A `switch` statement.
    Switch(TypedExpr, Box<TypedStmt>),
    /// A `case` statement.
    Case(TypedExpr, Box<TypedStmt>),
    /// A `default` statement in a `switch`.
    Default(Box<TypedStmt>),
    /// A labeled statement.
    Label(StringId, Box<TypedStmt>),
    /// A `goto` statement.
    Goto(StringId),
    /// A variable declaration.
    Declaration(TypeId, ThinVec<TypedDeclarator>, bool),
    FunctionDeclaration {
        ty: TypeId,
        name: StringId,
        params: ThinVec<TypedParameter>,
        is_variadic: bool,
        is_inline: bool,
        is_noreturn: bool,
    },
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<TypedStmt>, TypedExpr),
    /// An empty statement.
    Empty,
    /// An expression statement.
    Expr(TypedExpr),
    /// A `_Static_assert` declaration.
    StaticAssert(Box<TypedExpr>, StringId),
}

/// Represents a typed function declaration with type information.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedFunctionDecl {
    /// The return type of the function.
    pub return_type: TypeId,
    /// The name of the function.
    pub name: StringId,
    /// The parameters of the function.
    pub params: ThinVec<TypedParameter>,
    /// The body of the function.
    pub body: ThinVec<TypedStmt>,
    /// Whether the function is declared as inline.
    pub is_inline: bool,
    /// Whether the function is variadic.
    pub is_variadic: bool,
    /// Whether the function is declared as noreturn.
    pub is_noreturn: bool,
}

/// Represents a typed translation unit (program) with type information.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct TypedTranslationUnit {
    /// The global variables.
    pub globals: ThinVec<TypedStmt>, // TODO: hapus ini karena kelihatannya cuma dipakai untuk builtins
    /// The functions in the program.
    pub functions: ThinVec<TypedFunctionDecl>,
}

impl TypedExpr {
    pub fn get_logical_expr(&self) -> Option<(crate::parser::ast::LogicalOp, &TypedExpr, &TypedExpr)> {
        match self {
            TypedExpr::LogicalAnd(lhs, rhs, _, _) => Some((crate::parser::ast::LogicalOp::And, lhs, rhs)),
            TypedExpr::LogicalOr(lhs, rhs, _, _) => Some((crate::parser::ast::LogicalOp::Or, lhs, rhs)),
            _ => None,
        }
    }

    pub fn get_binary_expr(&self) -> Option<(crate::parser::ast::BinOp, &TypedExpr, &TypedExpr)> {
        if let Some((logical_op, lhs, rhs)) = self.get_logical_expr() {
            Some((logical_op.to_binop(), lhs, rhs))
        } else {
            match self {
                TypedExpr::Add(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Add, lhs, rhs)),
                TypedExpr::Sub(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Sub, lhs, rhs)),
                TypedExpr::Mul(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Mul, lhs, rhs)),
                TypedExpr::Div(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Div, lhs, rhs)),
                TypedExpr::Mod(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Mod, lhs, rhs)),
                TypedExpr::Equal(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Equal, lhs, rhs)),
                TypedExpr::NotEqual(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::NotEqual, lhs, rhs)),
                TypedExpr::LessThan(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::LessThan, lhs, rhs)),
                TypedExpr::GreaterThan(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::GreaterThan, lhs, rhs)),
                TypedExpr::LessThanOrEqual(lhs, rhs, _, _) => {
                    Some((crate::parser::ast::BinOp::LessThanOrEqual, lhs, rhs))
                }
                TypedExpr::GreaterThanOrEqual(lhs, rhs, _, _) => {
                    Some((crate::parser::ast::BinOp::GreaterThanOrEqual, lhs, rhs))
                }
                TypedExpr::LeftShift(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::LeftShift, lhs, rhs)),
                TypedExpr::RightShift(lhs, rhs, _, _) => Some((BinOp::RightShift, lhs, rhs)),
                TypedExpr::BitwiseOr(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::BitwiseOr, lhs, rhs)),
                TypedExpr::BitwiseXor(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::BitwiseXor, lhs, rhs)),
                TypedExpr::BitwiseAnd(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::BitwiseAnd, lhs, rhs)),
                TypedExpr::Comma(lhs, rhs, _, _) => Some((crate::parser::ast::BinOp::Comma, lhs, rhs)),
                _ => None,
            }
        }
    }

    pub fn get_assign_expr(&self) -> Option<(crate::parser::ast::AssignOp, &TypedLValue, &TypedExpr)> {
        match self {
            TypedExpr::Assign(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::Assign, lhs, rhs)),
            TypedExpr::AssignAdd(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::Add, lhs, rhs)),
            TypedExpr::AssignSub(lhs, rhs, _, _) => Some((AssignOp::Sub, lhs, rhs)),
            TypedExpr::AssignMul(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::Mul, lhs, rhs)),
            TypedExpr::AssignDiv(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::Div, lhs, rhs)),
            TypedExpr::AssignMod(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::Mod, lhs, rhs)),
            TypedExpr::AssignLeftShift(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::LeftShift, lhs, rhs)),
            TypedExpr::AssignRightShift(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::RightShift, lhs, rhs)),
            TypedExpr::AssignBitwiseAnd(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::BitwiseAnd, lhs, rhs)),
            TypedExpr::AssignBitwiseXor(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::BitwiseXor, lhs, rhs)),
            TypedExpr::AssignBitwiseOr(lhs, rhs, _, _) => Some((crate::parser::ast::AssignOp::BitwiseOr, lhs, rhs)),
            _ => None,
        }
    }

    pub fn ty(&self) -> TypeId {
        match self {
            TypedExpr::Number(_, _, ty) => *ty,
            TypedExpr::FloatNumber(_, _, ty) => *ty,
            TypedExpr::String(_, _, ty) => *ty,
            TypedExpr::Char(_, _, ty) => *ty,
            TypedExpr::Variable(_, _, ty) => *ty,
            TypedExpr::Call(_, _, _, ty) => *ty,
            TypedExpr::Assign(_, _, _, ty) => *ty,
            TypedExpr::AssignAdd(_, _, _, ty) => *ty,
            TypedExpr::AssignSub(_, _, _, ty) => *ty,
            TypedExpr::AssignMul(_, _, _, ty) => *ty,
            TypedExpr::AssignDiv(_, _, _, ty) => *ty,
            TypedExpr::AssignMod(_, _, _, ty) => *ty,
            TypedExpr::AssignLeftShift(_, _, _, ty) => *ty,
            TypedExpr::AssignRightShift(_, _, _, ty) => *ty,
            TypedExpr::AssignBitwiseAnd(_, _, _, ty) => *ty,
            TypedExpr::AssignBitwiseXor(_, _, _, ty) => *ty,
            TypedExpr::AssignBitwiseOr(_, _, _, ty) => *ty,
            TypedExpr::Add(_, _, _, ty) => *ty,
            TypedExpr::Sub(_, _, _, ty) => *ty,
            TypedExpr::Mul(_, _, _, ty) => *ty,
            TypedExpr::Div(_, _, _, ty) => *ty,
            TypedExpr::Mod(_, _, _, ty) => *ty,
            TypedExpr::Equal(_, _, _, ty) => *ty,
            TypedExpr::NotEqual(_, _, _, ty) => *ty,
            TypedExpr::LessThan(_, _, _, ty) => *ty,
            TypedExpr::GreaterThan(_, _, _, ty) => *ty,
            TypedExpr::LessThanOrEqual(_, _, _, ty) => *ty,
            TypedExpr::GreaterThanOrEqual(_, _, _, ty) => *ty,
            TypedExpr::LogicalAnd(_, _, _, ty) => *ty,
            TypedExpr::LogicalOr(_, _, _, ty) => *ty,
            TypedExpr::BitwiseOr(_, _, _, ty) => *ty,
            TypedExpr::BitwiseXor(_, _, _, ty) => *ty,
            TypedExpr::BitwiseAnd(_, _, _, ty) => *ty,
            TypedExpr::LeftShift(_, _, _, ty) => *ty,
            TypedExpr::RightShift(_, _, _, ty) => *ty,
            TypedExpr::Comma(_, _, _, ty) => *ty,
            TypedExpr::Neg(_, _, ty) => *ty,
            TypedExpr::LogicalNot(_, _, ty) => *ty,
            TypedExpr::BitwiseNot(_, _, ty) => *ty,
            TypedExpr::Sizeof(_, _, ty) => *ty,
            TypedExpr::Deref(_, _, ty) => *ty,
            TypedExpr::AddressOf(_, _, ty) => *ty,
            TypedExpr::SizeofType(_, _, ty) => *ty,
            TypedExpr::Alignof(_, _, ty) => *ty,
            TypedExpr::AlignofType(_, _, ty) => *ty,
            TypedExpr::Ternary(_, _, _, _, ty) => *ty,
            TypedExpr::Member(_, _, _, ty) => *ty,
            TypedExpr::PointerMember(_, _, _, ty) => *ty,
            TypedExpr::InitializerList(_, _, ty) => *ty,
            TypedExpr::ExplicitCast(_, _, _, ty) => *ty,
            TypedExpr::ImplicitCast(_, _, _, ty) => *ty,
            TypedExpr::CompoundLiteral(_, _, _, ty) => *ty,
            TypedExpr::PreIncrement(_, _, ty) => *ty,
            TypedExpr::PreDecrement(_, _, ty) => *ty,
            TypedExpr::PostIncrement(_, _, ty) => *ty,
            TypedExpr::PostDecrement(_, _, ty) => *ty,
        }
    }

    pub fn implicit_cast(self, to_ty: TypeId) -> TypedExpr {
        if self.ty() == to_ty {
            self
        } else {
            TypedExpr::ImplicitCast(
                to_ty,
                Box::new(self),
                SourceSpan::default(),
                to_ty,
            )
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            TypedExpr::Number(_, span, _) => *span,
            TypedExpr::FloatNumber(_, span, _) => *span,
            TypedExpr::String(_, span, _) => *span,
            TypedExpr::Char(_, span, _) => *span,
            TypedExpr::Variable(_, span, _) => *span,
            TypedExpr::Call(_, _, span, _) => *span,
            TypedExpr::Assign(_, _, span, _) => *span,
            TypedExpr::AssignAdd(_, _, span, _) => *span,
            TypedExpr::AssignSub(_, _, span, _) => *span,
            TypedExpr::AssignMul(_, _, span, _) => *span,
            TypedExpr::AssignDiv(_, _, span, _) => *span,
            TypedExpr::AssignMod(_, _, span, _) => *span,
            TypedExpr::AssignLeftShift(_, _, span, _) => *span,
            TypedExpr::AssignRightShift(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseAnd(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseXor(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseOr(_, _, span, _) => *span,
            TypedExpr::Add(_, _, span, _) => *span,
            TypedExpr::Sub(_, _, span, _) => *span,
            TypedExpr::Mul(_, _, span, _) => *span,
            TypedExpr::Div(_, _, span, _) => *span,
            TypedExpr::Mod(_, _, span, _) => *span,
            TypedExpr::Equal(_, _, span, _) => *span,
            TypedExpr::NotEqual(_, _, span, _) => *span,
            TypedExpr::LessThan(_, _, span, _) => *span,
            TypedExpr::GreaterThan(_, _, span, _) => *span,
            TypedExpr::LessThanOrEqual(_, _, span, _) => *span,
            TypedExpr::GreaterThanOrEqual(_, _, span, _) => *span,
            TypedExpr::LogicalAnd(_, _, span, _) => *span,
            TypedExpr::LogicalOr(_, _, span, _) => *span,
            TypedExpr::BitwiseOr(_, _, span, _) => *span,
            TypedExpr::BitwiseXor(_, _, span, _) => *span,
            TypedExpr::BitwiseAnd(_, _, span, _) => *span,
            TypedExpr::LeftShift(_, _, span, _) => *span,
            TypedExpr::RightShift(_, _, span, _) => *span,
            TypedExpr::Comma(_, _, span, _) => *span,
            TypedExpr::Neg(_, span, _) => *span,
            TypedExpr::LogicalNot(_, span, _) => *span,
            TypedExpr::BitwiseNot(_, span, _) => *span,
            TypedExpr::Sizeof(_, span, _) => *span,
            TypedExpr::Deref(_, span, _) => *span,
            TypedExpr::AddressOf(_, span, _) => *span,
            TypedExpr::SizeofType(_, span, _) => *span,
            TypedExpr::Alignof(_, span, _) => *span,
            TypedExpr::AlignofType(_, span, _) => *span,
            TypedExpr::Ternary(_, _, _, span, _) => *span,
            TypedExpr::Member(_, _, span, _) => *span,
            TypedExpr::PointerMember(_, _, span, _) => *span,
            TypedExpr::InitializerList(_, span, _) => *span,
            TypedExpr::ExplicitCast(_, _, span, _) => *span,
            TypedExpr::ImplicitCast(_, _, span, _) => *span,
            TypedExpr::CompoundLiteral(_, _, span, _) => *span,
            TypedExpr::PreIncrement(_, span, _) => *span,
            TypedExpr::PreDecrement(_, span, _) => *span,
            TypedExpr::PostIncrement(_, span, _) => *span,
            TypedExpr::PostDecrement(_, span, _) => *span,
        }
    }
}