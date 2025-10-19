#[derive(Debug, PartialEq)]
pub enum Stmt {
    Return(Expr),
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Number(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub name: String,
    pub body: Stmt,
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub function: Function,
}
