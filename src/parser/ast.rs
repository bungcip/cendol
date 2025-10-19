#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Int,
    Char,
    Float,
    Double,
    Void,
    Pointer(Box<Type>),
    Array(Box<Type>, usize),
    Struct(Vec<Parameter>),
    Union(Vec<Parameter>),
    Enum(Vec<String>),
}

#[derive(Debug, PartialEq)]
pub enum Stmt {
    Return(Expr),
    If(Box<Expr>, Box<Stmt>, Option<Box<Stmt>>),
    While(Box<Expr>, Box<Stmt>),
    For(
        Option<Box<Expr>>,
        Option<Box<Expr>>,
        Option<Box<Expr>>,
        Box<Stmt>,
    ),
    Block(Vec<Stmt>),
    Switch(Box<Expr>, Box<Stmt>),
    Case(Box<Expr>, Box<Stmt>),
    Default(Box<Stmt>),
    Label(String, Box<Stmt>),
    Goto(String),
    Declaration(Type, String, Option<Box<Expr>>),
    Typedef(Type, String),
    Break,
    Continue,
    DoWhile(Box<Stmt>, Box<Expr>),
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Number(i64),
    Variable(String),
    Assign(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Equal(Box<Expr>, Box<Expr>),
    NotEqual(Box<Expr>, Box<Expr>),
    LessThan(Box<Expr>, Box<Expr>),
    GreaterThan(Box<Expr>, Box<Expr>),
    LessThanOrEqual(Box<Expr>, Box<Expr>),
    GreaterThanOrEqual(Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    LogicalAnd(Box<Expr>, Box<Expr>),
    LogicalOr(Box<Expr>, Box<Expr>),
    LogicalNot(Box<Expr>),
    Deref(Box<Expr>),
    AddressOf(Box<Expr>),
    Neg(Box<Expr>),
    Increment(Box<Expr>),
    Decrement(Box<Expr>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Parameter {
    pub ty: Type,
    pub name: String,
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub name: String,
    pub params: Vec<Parameter>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub globals: Vec<Stmt>,
    pub function: Function,
}
