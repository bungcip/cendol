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
}

impl Type {
    /// Returns `true` if the type is a pointer.
    pub fn is_pointer(&self) -> bool {
        matches!(self, Type::Pointer(_))
    }

    /// Returns `true` if the type is a float or double.
    pub fn is_float(&self) -> bool {
        matches!(self, Type::Float | Type::Double)
    }

    /// Returns `true` if the type is unsigned.
    pub fn is_unsigned(&self) -> bool {
        matches!(
            self,
            Type::UnsignedInt
                | Type::UnsignedChar
                | Type::UnsignedShort
                | Type::UnsignedLong
                | Type::UnsignedLongLong
        )
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
            _ => 0,
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
    Label(String, Box<Stmt>),
    /// A `goto` statement.
    Goto(String),
    /// A variable declaration.
    Declaration(Type, Vec<Declarator>),
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
}

/// Represents an expression in the C language.
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
    /// A pre-increment expression.
    Increment(Box<Expr>),
    /// A pre-decrement expression.
    Decrement(Box<Expr>),
    /// A post-increment expression.
    PostIncrement(Box<Expr>),
    /// A post-decrement expression.
    PostDecrement(Box<Expr>),
    /// A ternary conditional expression.
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// An initializer list expression.
    InitializerList(Vec<(Vec<Designator>, Box<Initializer>)>),
    /// A member access expression.
    Member(Box<Expr>, String),
    /// A pointer member access expression.
    PointerMember(Box<Expr>, String),
    /// A type cast expression.
    Cast(Box<Type>, Box<Expr>),
    /// A compound literal expression.
    CompoundLiteral(Box<Type>, Box<Initializer>),
    /// A comma expression.
    Comma(Box<Expr>, Box<Expr>),
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
    List(Vec<(Vec<Designator>, Box<Initializer>)>),
}

/// Represents a function parameter.
#[derive(Debug, PartialEq, Clone)]
pub struct Parameter {
    /// The type of the parameter.
    pub ty: Type,
    /// The name of the parameter.
    pub name: String,
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
pub struct Program {
    /// The global variables.
    pub globals: Vec<Stmt>,
    /// The functions in the program.
    pub functions: Vec<Function>,
}
