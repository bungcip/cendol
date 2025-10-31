use crate::common::SourceSpan;

/// Type alias for initializer lists.
pub type InitializerList = Vec<(Vec<Designator>, Box<Initializer>)>;

/// Type alias for typed initializer lists.
pub type TypedInitializerList = Vec<(Vec<TypedDesignator>, Box<TypedInitializer>)>;

/// Represents a type in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    /// The `int` type.
    Int,
    /// The `char` type.
    Char,
    /// The `short` type.
    Short,
    /// The `float` type.
    Float,
    /// The `double` type.
    Double,
    /// The `long` type.
    Long,
    /// The `long long` type.
    LongLong,
    /// The `unsigned int` type.
    UnsignedInt,
    /// The `unsigned char` type.
    UnsignedChar,
    /// The `unsigned short` type.
    UnsignedShort,
    /// The `unsigned long` type.
    UnsignedLong,
    /// The `unsigned long long` type.
    UnsignedLongLong,
    /// The `void` type.
    Void,
    /// The `_Bool` type.
    Bool,
    /// A pointer to another type.
    Pointer(Box<Type>),
    /// An array of a specific size.
    Array(Box<Type>, usize),
    /// A struct definition.
    Struct(Option<String>, Vec<Parameter>),
    /// A union definition.
    Union(Option<String>, Vec<Parameter>),
    /// An enum definition.
    Enum(
        Option<String>,
        Vec<(String, Option<Box<Expr>>, crate::common::SourceSpan)>,
    ),
    Const(Box<Type>),
}

impl Type {
    /// Returns `true` if the type is a pointer.
    pub fn is_pointer(&self) -> bool {
        match self {
            Type::Pointer(_) => true,
            Type::Const(ty) => ty.is_pointer(),
            _ => false,
        }
    }

    /// Returns `true` if the type is unsigned.
    pub fn is_unsigned(&self) -> bool {
        match self {
            Type::UnsignedInt
            | Type::UnsignedChar
            | Type::UnsignedShort
            | Type::UnsignedLong
            | Type::UnsignedLongLong => true,
            Type::Const(ty) => ty.is_unsigned(),
            _ => false,
        }
    }

    /// Returns the rank of an integer type.
    pub fn get_integer_rank(&self) -> i32 {
        match self {
            Type::Bool => 1,
            Type::Char | Type::UnsignedChar => 2,
            Type::Short | Type::UnsignedShort => 3,
            Type::Int | Type::UnsignedInt => 4,
            Type::Long | Type::UnsignedLong => 5,
            Type::LongLong | Type::UnsignedLongLong => 6,
            Type::Const(ty) => ty.get_integer_rank(),
            _ => 0,
        }
    }

    /// Returns `true` if the type is a floating-point type.
    pub fn is_floating(&self) -> bool {
        match self {
            Type::Float | Type::Double => true,
            Type::Const(ty) => ty.is_floating(),
            _ => false,
        }
    }

    /// Returns `true` if the type is numeric.
    pub fn is_numeric(&self) -> bool {
        match self {
            Type::Int
            | Type::Char
            | Type::Short
            | Type::Long
            | Type::LongLong
            | Type::Float
            | Type::Double
            | Type::Enum(_, _) => true,
            Type::Const(ty) => ty.is_numeric(),
            _ => false,
        }
    }

    /// Returns the arithmetic conversion rank for usual arithmetic conversions.
    pub fn get_arithmetic_rank(&self) -> i32 {
        match self {
            Type::Bool => 1,
            Type::Char | Type::UnsignedChar => 2,
            Type::Short | Type::UnsignedShort => 3,
            Type::Int | Type::UnsignedInt => 4,
            Type::Long | Type::UnsignedLong => 5,
            Type::LongLong | Type::UnsignedLongLong => 6,
            Type::Float => 7,
            Type::Double => 8,
            Type::Const(ty) => ty.get_arithmetic_rank(),
            _ => 0,
        }
    }

    /// Recursively unwraps `const` qualifiers from a type.
    pub fn unwrap_const(&self) -> &Type {
        match self {
            Type::Const(ty) => ty.unwrap_const(),
            _ => self,
        }
    }
}

/// Represents the initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum ForInit {
    /// A variable declaration.
    Declaration(Type, String, Option<Initializer>),
    /// An expression.
    Expr(Expr),
}

/// Represents a declarator, which includes the type modifiers (pointers, arrays) and the identifier.
#[derive(Debug, PartialEq, Clone)]
pub struct Declarator {
    pub ty: Type,
    pub name: String,
    pub initializer: Option<Initializer>,
    pub span: SourceSpan,
}

/// Represents a statement in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    /// A `return` statement.
    Return(Expr),
    /// An `if` statement.
    If(Box<Expr>, Box<Stmt>, Option<Box<Stmt>>),
    /// A `while` loop.
    While(Box<Expr>, Box<Stmt>),
    /// A `for` loop.
    For(
        Option<ForInit>,
        Option<Box<Expr>>,
        Option<Box<Expr>>,
        Box<Stmt>,
    ),
    /// A block of statements.
    Block(Vec<Stmt>),
    /// A `switch` statement.
    Switch(Box<Expr>, Box<Stmt>),
    /// A `case` statement.
    Case(Box<Expr>, Box<Stmt>),
    /// A `default` statement in a `switch`.
    Default(Box<Stmt>),
    /// A labeled statement.
    Label(String, Box<Stmt>, crate::common::SourceSpan),
    /// A `goto` statement.
    Goto(String, crate::common::SourceSpan),
    /// A variable declaration.
    Declaration(Type, Vec<Declarator>, bool),
    FunctionDeclaration(Type, String, Vec<Parameter>, bool),
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<Stmt>, Box<Expr>),
    /// An empty statement.
    Empty,
    /// An expression statement.
    Expr(Expr),
    /// A `_Static_assert` declaration.
    StaticAssert(Box<Expr>, String),
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
    Number(i64),
    /// A float number literal.
    FloatNumber(f64),
    /// A string literal.
    String(String),
    /// A character literal.
    Char(String),
    /// A variable.
    Variable(String, crate::common::SourceSpan),
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
    Call(String, Vec<Expr>, crate::common::SourceSpan),
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
    SizeofType(Type),
    /// An alignof expression.
    Alignof(Box<Expr>),
    /// An alignof type expression.
    AlignofType(Type),
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
    Member(Box<Expr>, String),
    /// A pointer member access expression.
    PointerMember(Box<Expr>, String),
    /// An explicit type cast expression.
    ExplicitCast(Box<Type>, Box<Expr>),
    /// An implicit type cast expression.
    ImplicitCast(Box<Type>, Box<Expr>),
    /// A compound literal expression.
    CompoundLiteral(Box<Type>, Box<Initializer>),
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
}

/// Represents a C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum Designator {
    /// An array designator, e.g., `[0]`.
    Index(Box<Expr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(String),
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
    pub ty: Type,
    /// The name of the parameter.
    pub name: String,
    /// The span of the parameter.
    pub span: SourceSpan,
}

/// Represents a function definition.
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    /// The return type of the function.
    pub return_type: Type,
    /// The name of the function.
    pub name: String,
    /// The parameters of the function.
    pub params: Vec<Parameter>,
    /// The body of the function.
    pub body: Vec<Stmt>,
    /// Whether the function is declared as inline.
    pub is_inline: bool,
    /// Whether the function is variadic.
    pub is_variadic: bool,
}

/// Represents a program.
#[derive(Debug, PartialEq, Clone)]
pub struct TranslationUnit {
    /// The global variables.
    pub globals: Vec<Stmt>,
    /// The functions in the program.
    pub functions: Vec<Function>,
}

/// Represents a typed expression with type information.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedExpr {
    Number(i64, Type),
    FloatNumber(f64, Type),
    String(String, Type),
    Char(String, Type),
    Variable(String, SourceSpan, Type),
    Call(String, Vec<TypedExpr>, SourceSpan, Type),
    Assign(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignAdd(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignSub(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignMul(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignDiv(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignMod(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignLeftShift(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignRightShift(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignBitwiseAnd(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignBitwiseXor(Box<TypedExpr>, Box<TypedExpr>, Type),
    AssignBitwiseOr(Box<TypedExpr>, Box<TypedExpr>, Type),
    Add(Box<TypedExpr>, Box<TypedExpr>, Type),
    Sub(Box<TypedExpr>, Box<TypedExpr>, Type),
    Mul(Box<TypedExpr>, Box<TypedExpr>, Type),
    Div(Box<TypedExpr>, Box<TypedExpr>, Type),
    Mod(Box<TypedExpr>, Box<TypedExpr>, Type),
    Equal(Box<TypedExpr>, Box<TypedExpr>, Type),
    NotEqual(Box<TypedExpr>, Box<TypedExpr>, Type),
    LessThan(Box<TypedExpr>, Box<TypedExpr>, Type),
    GreaterThan(Box<TypedExpr>, Box<TypedExpr>, Type),
    LessThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, Type),
    GreaterThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, Type),
    LogicalAnd(Box<TypedExpr>, Box<TypedExpr>, Type),
    LogicalOr(Box<TypedExpr>, Box<TypedExpr>, Type),
    BitwiseOr(Box<TypedExpr>, Box<TypedExpr>, Type),
    BitwiseXor(Box<TypedExpr>, Box<TypedExpr>, Type),
    BitwiseAnd(Box<TypedExpr>, Box<TypedExpr>, Type),
    LeftShift(Box<TypedExpr>, Box<TypedExpr>, Type),
    RightShift(Box<TypedExpr>, Box<TypedExpr>, Type),
    Comma(Box<TypedExpr>, Box<TypedExpr>, Type),
    Neg(Box<TypedExpr>, Type),
    LogicalNot(Box<TypedExpr>, Type),
    BitwiseNot(Box<TypedExpr>, Type),
    Sizeof(Box<TypedExpr>, Type),
    Deref(Box<TypedExpr>, Type),
    AddressOf(Box<TypedExpr>, Type),
    SizeofType(Type, Type),
    Alignof(Box<TypedExpr>, Type),
    AlignofType(Type, Type),
    Ternary(Box<TypedExpr>, Box<TypedExpr>, Box<TypedExpr>, Type),
    Member(Box<TypedExpr>, String, Type),
    PointerMember(Box<TypedExpr>, String, Type),
    InitializerList(TypedInitializerList, Type),
    ExplicitCast(Box<Type>, Box<TypedExpr>, Type),
    ImplicitCast(Box<Type>, Box<TypedExpr>, Type),
    CompoundLiteral(Box<Type>, Box<TypedInitializer>, Type),
    PreIncrement(Box<TypedExpr>, Type),
    PreDecrement(Box<TypedExpr>, Type),
    PostIncrement(Box<TypedExpr>, Type),
    PostDecrement(Box<TypedExpr>, Type),
}

impl TypedExpr {
    pub fn get_logical_expr(&self) -> Option<(LogicalOp, &TypedExpr, &TypedExpr)> {
        match self {
            TypedExpr::LogicalAnd(lhs, rhs, _) => Some((LogicalOp::And, lhs, rhs)),
            TypedExpr::LogicalOr(lhs, rhs, _) => Some((LogicalOp::Or, lhs, rhs)),
            _ => None,
        }
    }

    pub fn get_binary_expr(&self) -> Option<(BinOp, &TypedExpr, &TypedExpr)> {
        if let Some((logical_op, lhs, rhs)) = self.get_logical_expr() {
            Some((logical_op.to_binop(), lhs, rhs))
        } else {
            match self {
                TypedExpr::Add(lhs, rhs, _) => Some((BinOp::Add, lhs, rhs)),
                TypedExpr::Sub(lhs, rhs, _) => Some((BinOp::Sub, lhs, rhs)),
                TypedExpr::Mul(lhs, rhs, _) => Some((BinOp::Mul, lhs, rhs)),
                TypedExpr::Div(lhs, rhs, _) => Some((BinOp::Div, lhs, rhs)),
                TypedExpr::Mod(lhs, rhs, _) => Some((BinOp::Mod, lhs, rhs)),
                TypedExpr::Equal(lhs, rhs, _) => Some((BinOp::Equal, lhs, rhs)),
                TypedExpr::NotEqual(lhs, rhs, _) => Some((BinOp::NotEqual, lhs, rhs)),
                TypedExpr::LessThan(lhs, rhs, _) => Some((BinOp::LessThan, lhs, rhs)),
                TypedExpr::GreaterThan(lhs, rhs, _) => Some((BinOp::GreaterThan, lhs, rhs)),
                TypedExpr::LessThanOrEqual(lhs, rhs, _) => Some((BinOp::LessThanOrEqual, lhs, rhs)),
                TypedExpr::GreaterThanOrEqual(lhs, rhs, _) => {
                    Some((BinOp::GreaterThanOrEqual, lhs, rhs))
                }
                TypedExpr::LeftShift(lhs, rhs, _) => Some((BinOp::LeftShift, lhs, rhs)),
                TypedExpr::RightShift(lhs, rhs, _) => Some((BinOp::RightShift, lhs, rhs)),
                TypedExpr::BitwiseOr(lhs, rhs, _) => Some((BinOp::BitwiseOr, lhs, rhs)),
                TypedExpr::BitwiseXor(lhs, rhs, _) => Some((BinOp::BitwiseXor, lhs, rhs)),
                TypedExpr::BitwiseAnd(lhs, rhs, _) => Some((BinOp::BitwiseAnd, lhs, rhs)),
                TypedExpr::Comma(lhs, rhs, _) => Some((BinOp::Comma, lhs, rhs)),
                _ => None,
            }
        }
    }

    pub fn get_assign_expr(&self) -> Option<(AssignOp, &TypedExpr, &TypedExpr)> {
        match self {
            TypedExpr::Assign(lhs, rhs, _) => Some((AssignOp::Assign, lhs, rhs)),
            TypedExpr::AssignAdd(lhs, rhs, _) => Some((AssignOp::Add, lhs, rhs)),
            TypedExpr::AssignSub(lhs, rhs, _) => Some((AssignOp::Sub, lhs, rhs)),
            TypedExpr::AssignMul(lhs, rhs, _) => Some((AssignOp::Mul, lhs, rhs)),
            TypedExpr::AssignDiv(lhs, rhs, _) => Some((AssignOp::Div, lhs, rhs)),
            TypedExpr::AssignMod(lhs, rhs, _) => Some((AssignOp::Mod, lhs, rhs)),
            TypedExpr::AssignLeftShift(lhs, rhs, _) => Some((AssignOp::LeftShift, lhs, rhs)),
            TypedExpr::AssignRightShift(lhs, rhs, _) => Some((AssignOp::RightShift, lhs, rhs)),
            TypedExpr::AssignBitwiseAnd(lhs, rhs, _) => Some((AssignOp::BitwiseAnd, lhs, rhs)),
            TypedExpr::AssignBitwiseXor(lhs, rhs, _) => Some((AssignOp::BitwiseXor, lhs, rhs)),
            TypedExpr::AssignBitwiseOr(lhs, rhs, _) => Some((AssignOp::BitwiseOr, lhs, rhs)),
            _ => None,
        }
    }

    pub fn ty(&self) -> &Type {
        match self {
            TypedExpr::Number(_, ty) => ty,
            TypedExpr::FloatNumber(_, ty) => ty,
            TypedExpr::String(_, ty) => ty,
            TypedExpr::Char(_, ty) => ty,
            TypedExpr::Variable(_, _, ty) => ty,
            TypedExpr::Call(_, _, _, ty) => ty,
            TypedExpr::Assign(_, _, ty) => ty,
            TypedExpr::AssignAdd(_, _, ty) => ty,
            TypedExpr::AssignSub(_, _, ty) => ty,
            TypedExpr::AssignMul(_, _, ty) => ty,
            TypedExpr::AssignDiv(_, _, ty) => ty,
            TypedExpr::AssignMod(_, _, ty) => ty,
            TypedExpr::AssignLeftShift(_, _, ty) => ty,
            TypedExpr::AssignRightShift(_, _, ty) => ty,
            TypedExpr::AssignBitwiseAnd(_, _, ty) => ty,
            TypedExpr::AssignBitwiseXor(_, _, ty) => ty,
            TypedExpr::AssignBitwiseOr(_, _, ty) => ty,
            TypedExpr::Add(_, _, ty) => ty,
            TypedExpr::Sub(_, _, ty) => ty,
            TypedExpr::Mul(_, _, ty) => ty,
            TypedExpr::Div(_, _, ty) => ty,
            TypedExpr::Mod(_, _, ty) => ty,
            TypedExpr::Equal(_, _, ty) => ty,
            TypedExpr::NotEqual(_, _, ty) => ty,
            TypedExpr::LessThan(_, _, ty) => ty,
            TypedExpr::GreaterThan(_, _, ty) => ty,
            TypedExpr::LessThanOrEqual(_, _, ty) => ty,
            TypedExpr::GreaterThanOrEqual(_, _, ty) => ty,
            TypedExpr::LogicalAnd(_, _, ty) => ty,
            TypedExpr::LogicalOr(_, _, ty) => ty,
            TypedExpr::BitwiseOr(_, _, ty) => ty,
            TypedExpr::BitwiseXor(_, _, ty) => ty,
            TypedExpr::BitwiseAnd(_, _, ty) => ty,
            TypedExpr::LeftShift(_, _, ty) => ty,
            TypedExpr::RightShift(_, _, ty) => ty,
            TypedExpr::Comma(_, _, ty) => ty,
            TypedExpr::Neg(_, ty) => ty,
            TypedExpr::LogicalNot(_, ty) => ty,
            TypedExpr::BitwiseNot(_, ty) => ty,
            TypedExpr::Sizeof(_, ty) => ty,
            TypedExpr::Deref(_, ty) => ty,
            TypedExpr::AddressOf(_, ty) => ty,
            TypedExpr::SizeofType(_, ty) => ty,
            TypedExpr::Alignof(_, ty) => ty,
            TypedExpr::AlignofType(_, ty) => ty,
            TypedExpr::Ternary(_, _, _, ty) => ty,
            TypedExpr::Member(_, _, ty) => ty,
            TypedExpr::PointerMember(_, _, ty) => ty,
            TypedExpr::InitializerList(_, ty) => ty,
            TypedExpr::ExplicitCast(_, _, ty) => ty,
            TypedExpr::ImplicitCast(_, _, ty) => ty,
            TypedExpr::CompoundLiteral(_, _, ty) => ty,
            TypedExpr::PreIncrement(_, ty) => ty,
            TypedExpr::PreDecrement(_, ty) => ty,
            TypedExpr::PostIncrement(_, ty) => ty,
            TypedExpr::PostDecrement(_, ty) => ty,
        }
    }

    pub fn implicit_cast(self, to_ty: Type) -> TypedExpr {
        if self.ty() == &to_ty {
            self
        } else {
            TypedExpr::ImplicitCast(Box::new(to_ty.clone()), Box::new(self), to_ty)
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            TypedExpr::Variable(_, span, _) => *span,
            TypedExpr::Call(_, _, span, _) => *span,
            _ => SourceSpan::new(
                crate::file::FileId(0),
                crate::common::SourceLocation::new(crate::file::FileId(0), 0, 0),
                crate::common::SourceLocation::new(crate::file::FileId(0), 0, 0),
            ),
        }
    }
}

/// Represents a typed C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedDesignator {
    /// An array designator, e.g., `[0]`.
    Index(Box<TypedExpr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(String),
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
    pub ty: Type,
    pub name: String,
    pub initializer: Option<TypedInitializer>,
}

/// Represents the typed initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedForInit {
    /// A variable declaration.
    Declaration(Type, String, Option<TypedInitializer>),
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
    Block(Vec<TypedStmt>),
    /// A `switch` statement.
    Switch(TypedExpr, Box<TypedStmt>),
    /// A `case` statement.
    Case(TypedExpr, Box<TypedStmt>),
    /// A `default` statement in a `switch`.
    Default(Box<TypedStmt>),
    /// A labeled statement.
    Label(String, Box<TypedStmt>),
    /// A `goto` statement.
    Goto(String),
    /// A variable declaration.
    Declaration(Type, Vec<TypedDeclarator>, bool),
    FunctionDeclaration(Type, String, Vec<Parameter>, bool),
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
    StaticAssert(Box<TypedExpr>, String),
}

/// Represents a typed function declaration with type information.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedFunctionDecl {
    /// The return type of the function.
    pub return_type: Type,
    /// The name of the function.
    pub name: String,
    /// The parameters of the function.
    pub params: Vec<Parameter>,
    /// The body of the function.
    pub body: Vec<TypedStmt>,
    /// Whether the function is declared as inline.
    pub is_inline: bool,
    /// Whether the function is variadic.
    pub is_variadic: bool,
}

/// Represents a typed translation unit (program) with type information.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct TypedTranslationUnit {
    /// The global variables.
    pub globals: Vec<TypedStmt>,
    /// The functions in the program.
    pub functions: Vec<TypedFunctionDecl>,
}
