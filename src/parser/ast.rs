/// Represents a type in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    /// The `int` type.
    Int,
    /// The `char` type.
    Char,
    /// The `float` type.
    Float,
    /// The `double` type.
    Double,
    /// The `long` type.
    Long,
    /// The `long long` type.
    LongLong,
    /// The `void` type.
    Void,
    /// The `_Bool` type.
    Bool,
    /// A pointer to another type.
    Pointer(Box<Type>),
    /// An array of a specific size.
    Array(Box<Type>, usize),
    /// A struct definition.
    Struct(Vec<Parameter>),
    /// A union definition.
    Union(Vec<Parameter>),
    /// An enum definition.
    Enum(Vec<String>),
}

/// Represents the initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum ForInit {
    /// A variable declaration.
    Declaration(Type, String, Option<Box<Expr>>),
    /// An expression.
    Expr(Expr),
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
    Declaration(Type, String, Option<Box<Expr>>),
    FunctionDeclaration(Type, String, Vec<Parameter>),
    /// A `typedef` statement.
    Typedef(Type, String),
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<Stmt>, Box<Expr>),
    /// An expression statement.
    Expr(Expr),
}

/// Represents an expression in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// A number literal.
    Number(i64),
    String(String),
    /// A variable.
    Variable(String),
    /// An assignment expression.
    Assign(Box<Expr>, Box<Expr>),
    /// An addition expression.
    Add(Box<Expr>, Box<Expr>),
    /// A subtraction expression.
    Sub(Box<Expr>, Box<Expr>),
    /// A multiplication expression.
    Mul(Box<Expr>, Box<Expr>),
    /// A division expression.
    Div(Box<Expr>, Box<Expr>),
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
    /// A function call.
    Call(String, Vec<Expr>),
    /// A logical AND expression.
    LogicalAnd(Box<Expr>, Box<Expr>),
    /// A logical OR expression.
    LogicalOr(Box<Expr>, Box<Expr>),
    /// A logical NOT expression.
    LogicalNot(Box<Expr>),
    /// A dereference expression.
    Deref(Box<Expr>),
    /// An address-of expression.
    AddressOf(Box<Expr>),
    /// A negation expression.
    Neg(Box<Expr>),
    /// A pre-increment expression.
    Increment(Box<Expr>),
    /// A pre-decrement expression.
    Decrement(Box<Expr>),
    /// A ternary conditional expression.
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
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
#[derive(Debug, PartialEq)]
pub struct Function {
    /// The name of the function.
    pub name: String,
    /// The parameters of the function.
    pub params: Vec<Parameter>,
    /// The body of the function.
    pub body: Vec<Stmt>,
}

/// Represents a program.
#[derive(Debug, PartialEq)]
pub struct Program {
    /// The global variables.
    pub globals: Vec<Stmt>,
    /// The main function.
    pub function: Function,
}
