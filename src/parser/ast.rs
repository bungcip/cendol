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
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Number(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Cmp(Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub name: String,
    pub body: Box<Stmt>,
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub function: Function,
}
