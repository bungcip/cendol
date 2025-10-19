use crate::parser::ast::{Expr, Function, Parameter, Program, Stmt, Type};
use crate::parser::error::ParserError;
use crate::parser::token::{KeywordKind, PunctKind, Token, TokenKind};
use crate::preprocessor;

pub mod ast;
pub mod error;
pub mod token;

/// A parser that converts a stream of tokens into an abstract syntax tree.
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    /// Creates a new `Parser`.
    ///
    /// # Arguments
    ///
    /// * `tokens` - A vector of preprocessor tokens.
    ///
    /// # Returns
    ///
    /// A `Result` containing the new `Parser` instance, or a `ParserError` if tokenization fails.
    pub fn new(tokens: Vec<preprocessor::token::Token>) -> Result<Self, ParserError> {
        let tokens = tokens
            .into_iter()
            .filter(|t| {
                !matches!(
                    t.kind,
                    preprocessor::token::TokenKind::Whitespace(_)
                        | preprocessor::token::TokenKind::Newline
                )
            })
            .map(|t| t.into())
            .collect();

        let parser = Parser {
            tokens,
            position: 0,
        };
        Ok(parser)
    }

    /// Returns the current token without consuming it.
    fn current_token(&self) -> Result<Token, ParserError> {
        self.tokens
            .get(self.position)
            .cloned()
            .ok_or(ParserError::UnexpectedEof)
    }

    /// Consumes the current token.
    fn eat(&mut self) -> Result<(), ParserError> {
        self.position += 1;
        Ok(())
    }

    /// Expects a specific punctuation token.
    fn expect_punct(&mut self, value: PunctKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Punct(p) = token.kind.clone()
            && p == value
        {
            self.eat()?;
            return Ok(());
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    /// Expects a specific identifier.
    fn expect_identifier(&mut self, value: &str) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind.clone()
            && id == value
        {
            self.eat()?;
            return Ok(());
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    /// Expects a specific keyword.
    fn expect_keyword(&mut self, value: KeywordKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone()
            && k == value
        {
            self.eat()?;
            return Ok(());
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    /// Parses a type.
    fn parse_type(&mut self) -> Result<Type, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone() {
            let ty = match k {
                KeywordKind::Int => Type::Int,
                KeywordKind::Char => Type::Char,
                KeywordKind::Float => Type::Float,
                KeywordKind::Double => Type::Double,
                KeywordKind::Void => Type::Void,
                KeywordKind::Struct => {
                    self.eat()?;
                    self.expect_punct(PunctKind::LeftBrace)?;
                    let mut members = Vec::new();
                    while let Ok(t) = self.current_token() {
                        if let TokenKind::Punct(PunctKind::RightBrace) = t.kind {
                            self.eat()?;
                            break;
                        }
                        let ty = self.parse_type()?;
                        let token = self.current_token()?;
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            members.push(Parameter { ty, name: id });
                        }
                        self.expect_punct(PunctKind::Semicolon)?;
                    }
                    Type::Struct(members)
                }
                KeywordKind::Union => {
                    self.eat()?;
                    self.expect_punct(PunctKind::LeftBrace)?;
                    let mut members = Vec::new();
                    while let Ok(t) = self.current_token() {
                        if let TokenKind::Punct(PunctKind::RightBrace) = t.kind {
                            self.eat()?;
                            break;
                        }
                        let ty = self.parse_type()?;
                        let token = self.current_token()?;
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            members.push(Parameter { ty, name: id });
                        }
                        self.expect_punct(PunctKind::Semicolon)?;
                    }
                    Type::Union(members)
                }
                KeywordKind::Enum => {
                    self.eat()?;
                    self.expect_punct(PunctKind::LeftBrace)?;
                    let mut enumerators = Vec::new();
                    while let Ok(t) = self.current_token() {
                        if let TokenKind::Punct(PunctKind::RightBrace) = t.kind {
                            self.eat()?;
                            break;
                        }
                        let token = self.current_token()?;
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            enumerators.push(id);
                        }
                        if let Ok(t) = self.current_token()
                            && let TokenKind::Punct(PunctKind::Comma) = t.kind
                        {
                            self.eat()?;
                        }
                    }
                    Type::Enum(enumerators)
                }
                _ => return Err(ParserError::UnexpectedToken(token)),
            };
            self.eat()?;
            let mut ty = ty;
            while let Ok(token) = self.current_token() {
                if let TokenKind::Punct(p) = token.kind.clone() {
                    if p == PunctKind::Star {
                        self.eat()?;
                        ty = Type::Pointer(Box::new(ty));
                    } else if p == PunctKind::LeftBracket {
                        self.eat()?;
                        let size = self.parse_expr()?;
                        if let Expr::Number(n) = size {
                            ty = Type::Array(Box::new(ty), n as usize);
                        } else {
                            return Err(ParserError::UnexpectedToken(token));
                        }
                        self.expect_punct(PunctKind::RightBracket)?;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            Ok(ty)
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses an expression.
    fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        self.parse_pratt_expr(0)
    }

    /// Gets the infix binding power of a token.
    fn infix_binding_power(&self, kind: &TokenKind) -> Option<(u8, u8)> {
        match kind {
            TokenKind::Punct(PunctKind::Equal) => Some((2, 1)),
            TokenKind::Punct(PunctKind::PipePipe) => Some((3, 4)),
            TokenKind::Punct(PunctKind::AmpersandAmpersand) => Some((5, 6)),
            TokenKind::Punct(PunctKind::EqualEqual) | TokenKind::Punct(PunctKind::BangEqual) => {
                Some((7, 8))
            }
            TokenKind::Punct(PunctKind::LessThan)
            | TokenKind::Punct(PunctKind::GreaterThan)
            | TokenKind::Punct(PunctKind::LessThanEqual)
            | TokenKind::Punct(PunctKind::GreaterThanEqual) => Some((9, 10)),
            TokenKind::Punct(PunctKind::Plus) | TokenKind::Punct(PunctKind::Minus) => {
                Some((11, 12))
            }
            TokenKind::Punct(PunctKind::Star) | TokenKind::Punct(PunctKind::Slash) => {
                Some((13, 14))
            }
            _ => None,
        }
    }

    /// Gets the prefix binding power of a token.
    #[allow(dead_code)]
    fn prefix_binding_power(&self, kind: &TokenKind) -> Option<((), u8)> {
        match kind {
            TokenKind::Punct(PunctKind::Plus) | TokenKind::Punct(PunctKind::Minus) => {
                Some(((), 15))
            }
            TokenKind::Punct(PunctKind::Bang) => Some(((), 15)),
            _ => None,
        }
    }

    /// Gets the postfix binding power of a token.
    fn postfix_binding_power(&self, kind: &TokenKind) -> Option<(u8, ())> {
        match kind {
            TokenKind::Punct(PunctKind::PlusPlus) | TokenKind::Punct(PunctKind::MinusMinus) => {
                Some((16, ()))
            }
            _ => None,
        }
    }

    /// Parses an expression using the Pratt parsing algorithm.
    fn parse_pratt_expr(&mut self, min_bp: u8) -> Result<Expr, ParserError> {
        let mut lhs = self.parse_primary()?;

        loop {
            let token = self.current_token()?;
            if let Some((l_bp, ())) = self.postfix_binding_power(&token.kind) {
                if l_bp < min_bp {
                    break;
                }

                self.eat()?;

                lhs = match token.kind {
                    TokenKind::Punct(PunctKind::PlusPlus) => Expr::Increment(Box::new(lhs)),
                    TokenKind::Punct(PunctKind::MinusMinus) => Expr::Decrement(Box::new(lhs)),
                    _ => unreachable!(),
                };
                continue;
            }
            if let Some((l_bp, r_bp)) = self.infix_binding_power(&token.kind) {
                if l_bp < min_bp {
                    break;
                }

                self.eat()?;
                let rhs = self.parse_pratt_expr(r_bp)?;

                lhs = match token.kind {
                    TokenKind::Punct(PunctKind::Equal) => {
                        Expr::Assign(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::Plus) => Expr::Add(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Minus) => Expr::Sub(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Star) => Expr::Mul(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Slash) => Expr::Div(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::EqualEqual) => {
                        Expr::Equal(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::BangEqual) => {
                        Expr::NotEqual(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::LessThan) => {
                        Expr::LessThan(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::GreaterThan) => {
                        Expr::GreaterThan(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::LessThanEqual) => {
                        Expr::LessThanOrEqual(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::GreaterThanEqual) => {
                        Expr::GreaterThanOrEqual(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::AmpersandAmpersand) => {
                        Expr::LogicalAnd(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Punct(PunctKind::PipePipe) => {
                        Expr::LogicalOr(Box::new(lhs), Box::new(rhs))
                    }
                    _ => unreachable!(),
                };
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    /// Parses a primary expression.
    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.eat()?;
                Ok(Expr::Number(n.parse().unwrap()))
            }
            TokenKind::Identifier(name) => {
                self.eat()?;
                let token = self.current_token()?;
                if let TokenKind::Punct(PunctKind::LeftParen) = token.kind {
                    self.eat()?;
                    let mut args = Vec::new();
                    while let Ok(t) = self.current_token() {
                        if let TokenKind::Punct(PunctKind::RightParen) = t.kind {
                            self.eat()?;
                            break;
                        }
                        args.push(self.parse_expr()?);
                        if let Ok(t) = self.current_token()
                            && let TokenKind::Punct(PunctKind::Comma) = t.kind
                        {
                            self.eat()?;
                        }
                    }
                    Ok(Expr::Call(name, args))
                } else {
                    Ok(Expr::Variable(name))
                }
            }
            TokenKind::Punct(p) => match p {
                PunctKind::Star => {
                    self.eat()?;
                    let expr = self.parse_primary()?;
                    Ok(Expr::Deref(Box::new(expr)))
                }
                PunctKind::Ampersand => {
                    self.eat()?;
                    let expr = self.parse_primary()?;
                    Ok(Expr::AddressOf(Box::new(expr)))
                }
                PunctKind::Minus => {
                    self.eat()?;
                    let expr = self.parse_pratt_expr(7)?;
                    Ok(Expr::Neg(Box::new(expr)))
                }
                PunctKind::Plus => {
                    self.eat()?;
                    self.parse_pratt_expr(7)
                }
                PunctKind::Bang => {
                    self.eat()?;
                    let expr = self.parse_pratt_expr(15)?;
                    Ok(Expr::LogicalNot(Box::new(expr)))
                }
                _ => Err(ParserError::UnexpectedToken(token.clone())),
            },
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }

    /// Parses a statement.
    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Punct(p) = token.kind.clone() {
            if p == PunctKind::LeftBrace {
                self.eat()?;
                let mut stmts = Vec::new();
                while let Ok(t) = self.current_token() {
                    if let TokenKind::Punct(p) = t.kind
                        && p == PunctKind::RightBrace
                    {
                        self.eat()?;
                        break;
                    }
                    stmts.push(self.parse_stmt()?);
                }
                return Ok(Stmt::Block(stmts));
            }
        } else if let Ok(ty) = self.parse_type() {
            let token = self.current_token()?;
            if let TokenKind::Identifier(id) = token.kind.clone() {
                self.eat()?;
                let mut initializer = None;
                if let Ok(t) = self.current_token()
                    && let TokenKind::Punct(PunctKind::Equal) = t.kind
                {
                    self.eat()?;
                    initializer = Some(Box::new(self.parse_expr()?));
                }
                self.expect_punct(PunctKind::Semicolon)?;
                return Ok(Stmt::Declaration(ty, id, initializer));
            }
        } else if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == KeywordKind::Return {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(PunctKind::Semicolon)?;
                return Ok(Stmt::Return(expr));
            } else if k == KeywordKind::If {
                self.eat()?;
                self.expect_punct(PunctKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(PunctKind::RightParen)?;
                let then = self.parse_stmt()?;
                let mut else_stmt = None;
                let next_token = self.current_token()?;
                if let TokenKind::Keyword(k) = next_token.kind.clone()
                    && k == KeywordKind::Else
                {
                    self.eat()?;
                    else_stmt = Some(Box::new(self.parse_stmt()?));
                }
                return Ok(Stmt::If(Box::new(cond), Box::new(then), else_stmt));
            } else if k == KeywordKind::While {
                self.eat()?;
                self.expect_punct(PunctKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(PunctKind::RightParen)?;
                let body = self.parse_stmt()?;
                return Ok(Stmt::While(Box::new(cond), Box::new(body)));
            } else if k == KeywordKind::For {
                self.eat()?;
                self.expect_punct(PunctKind::LeftParen)?;
                let init = Some(Box::new(self.parse_expr()?));
                self.expect_punct(PunctKind::Semicolon)?;
                let cond = Some(Box::new(self.parse_expr()?));
                self.expect_punct(PunctKind::Semicolon)?;
                let inc = Some(Box::new(self.parse_expr()?));
                self.expect_punct(PunctKind::RightParen)?;
                let body = self.parse_stmt()?;
                return Ok(Stmt::For(init, cond, inc, Box::new(body)));
            } else if k == KeywordKind::Switch {
                self.eat()?;
                self.expect_punct(PunctKind::LeftParen)?;
                let expr = self.parse_expr()?;
                self.expect_punct(PunctKind::RightParen)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Switch(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Case {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(PunctKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Case(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Default {
                self.eat()?;
                self.expect_punct(PunctKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Default(Box::new(stmt)));
            } else if k == KeywordKind::Goto {
                self.eat()?;
                let token = self.current_token()?;
                if let TokenKind::Identifier(id) = token.kind.clone() {
                    self.eat()?;
                    self.expect_punct(PunctKind::Semicolon)?;
                    return Ok(Stmt::Goto(id));
                }
            } else if k == KeywordKind::Break {
                self.eat()?;
                self.expect_punct(PunctKind::Semicolon)?;
                return Ok(Stmt::Break);
            } else if k == KeywordKind::Continue {
                self.eat()?;
                self.expect_punct(PunctKind::Semicolon)?;
                return Ok(Stmt::Continue);
            } else if k == KeywordKind::Do {
                self.eat()?;
                let body = self.parse_stmt()?;
                self.expect_keyword(KeywordKind::While)?;
                self.expect_punct(PunctKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(PunctKind::RightParen)?;
                self.expect_punct(PunctKind::Semicolon)?;
                return Ok(Stmt::DoWhile(Box::new(body), Box::new(cond)));
            } else if k == KeywordKind::Typedef {
                self.eat()?;
                let ty = self.parse_type()?;
                let token = self.current_token()?;
                if let TokenKind::Identifier(id) = token.kind.clone() {
                    self.eat()?;
                    self.expect_punct(PunctKind::Semicolon)?;
                    return Ok(Stmt::Typedef(ty, id));
                }
            }
        }

        let expr = self.parse_expr()?;
        self.expect_punct(PunctKind::Semicolon)?;
        Ok(Stmt::Expr(expr))
    }

    /// Parses a function.
    fn parse_function(&mut self) -> Result<Function, ParserError> {
        let _ty = self.parse_type()?;
        self.expect_identifier("main")?;
        self.expect_punct(PunctKind::LeftParen)?;
        let mut params = Vec::new();
        while let Ok(t) = self.current_token() {
            if let TokenKind::Punct(PunctKind::RightParen) = t.kind {
                self.eat()?;
                break;
            }
            let ty = self.parse_type()?;
            let token = self.current_token()?;
            if let TokenKind::Identifier(id) = token.kind.clone() {
                self.eat()?;
                params.push(Parameter { ty, name: id });
            }
            if let Ok(t) = self.current_token()
                && let TokenKind::Punct(PunctKind::Comma) = t.kind
            {
                self.eat()?;
            }
        }
        self.expect_punct(PunctKind::LeftBrace)?;
        let mut stmts = Vec::new();
        while let Ok(t) = self.current_token() {
            if let TokenKind::Punct(p) = t.kind
                && p == PunctKind::RightBrace
            {
                self.eat()?;
                break;
            }
            stmts.push(self.parse_stmt()?);
        }
        Ok(Function {
            name: "main".to_string(),
            params,
            body: stmts,
        })
    }

    /// Parses the entire program.
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `Program`, or a `ParserError` if parsing fails.
    pub fn parse(&mut self) -> Result<Program, ParserError> {
        let mut globals = Vec::new();
        while let Ok(ty) = self.parse_type() {
            let token = self.current_token()?;
            if let TokenKind::Identifier(id) = token.kind.clone() {
                self.eat()?;
                let token = self.current_token()?;
                if let TokenKind::Punct(PunctKind::LeftParen) = token.kind {
                    self.position -= 2;
                    break;
                }
                let mut initializer = None;
                if let Ok(t) = self.current_token()
                    && let TokenKind::Punct(PunctKind::Equal) = t.kind
                {
                    self.eat()?;
                    initializer = Some(Box::new(self.parse_expr()?));
                }
                self.expect_punct(PunctKind::Semicolon)?;
                globals.push(Stmt::Declaration(ty, id, initializer));
            }
        }
        let function = self.parse_function()?;
        Ok(Program { globals, function })
    }
}
