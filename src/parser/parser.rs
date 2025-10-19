use crate::parser::ast::{Expr, Function, Program, Stmt, Type};
use crate::parser::error::ParserError;
use crate::parser::token::{KeywordKind, PunctKind, Token, TokenKind};
use crate::preprocessor;

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
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

    fn current_token(&self) -> Result<Token, ParserError> {
        self.tokens
            .get(self.position)
            .cloned()
            .ok_or(ParserError::UnexpectedEof)
    }

    fn eat(&mut self) -> Result<(), ParserError> {
        self.position += 1;
        Ok(())
    }

    fn expect_punct(&mut self, value: PunctKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Punct(p) = token.kind.clone() {
            if p == value {
                self.eat()?;
                return Ok(());
            }
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    fn expect_identifier(&mut self, value: &str) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind.clone() {
            if id == value {
                self.eat()?;
                return Ok(());
            }
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    fn expect_keyword(&mut self, value: KeywordKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == value {
                self.eat()?;
                return Ok(());
            }
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        self.parse_pratt_expr(0)
    }

    fn infix_binding_power(&self, kind: &TokenKind) -> Option<(u8, u8)> {
        match kind {
            TokenKind::Punct(PunctKind::Equal) => Some((2, 1)),
            TokenKind::Punct(PunctKind::Plus) | TokenKind::Punct(PunctKind::Minus) => Some((3, 4)),
            TokenKind::Punct(PunctKind::Star) | TokenKind::Punct(PunctKind::Slash) => Some((5, 6)),
            _ => None,
        }
    }

    fn prefix_binding_power(&self, kind: &TokenKind) -> Option<((), u8)> {
        match kind {
            TokenKind::Punct(PunctKind::Plus) | TokenKind::Punct(PunctKind::Minus) => Some(((), 7)),
            _ => None,
        }
    }

    fn parse_pratt_expr(&mut self, min_bp: u8) -> Result<Expr, ParserError> {
        let mut lhs = self.parse_primary()?;

        loop {
            let token = self.current_token()?;
            if let Some((l_bp, r_bp)) = self.infix_binding_power(&token.kind) {
                if l_bp < min_bp {
                    break;
                }

                self.eat()?;
                let rhs = self.parse_pratt_expr(r_bp)?;

                lhs = match token.kind {
                    TokenKind::Punct(PunctKind::Equal) => Expr::Assign(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Plus) => Expr::Add(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Minus) => Expr::Sub(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Star) => Expr::Mul(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Punct(PunctKind::Slash) => Expr::Div(Box::new(lhs), Box::new(rhs)),
                    _ => unreachable!(),
                };
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.eat()?;
                Ok(Expr::Number(n.parse().unwrap()))
            }
            TokenKind::Identifier(name) => {
                self.eat()?;
                Ok(Expr::Variable(name))
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
                _ => Err(ParserError::UnexpectedToken(token.clone())),
            },
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Punct(p) = token.kind.clone() {
            if p == PunctKind::LeftBrace {
                self.eat()?;
                let mut stmts = Vec::new();
                while let Ok(t) = self.current_token() {
                    if let TokenKind::Punct(p) = t.kind {
                        if p == PunctKind::RightBrace {
                            self.eat()?;
                            break;
                        }
                    }
                    stmts.push(self.parse_stmt()?);
                }
                return Ok(Stmt::Block(stmts));
            }
        } else if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == KeywordKind::Int {
                self.eat()?;
                let mut ty = Type::Int;
                while let Ok(token) = self.current_token() {
                    if let TokenKind::Punct(p) = token.kind {
                        if p == PunctKind::Star {
                            self.eat()?;
                            ty = Type::Pointer(Box::new(ty));
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                let token = self.current_token()?;
                if let TokenKind::Identifier(id) = token.kind.clone() {
                    self.eat()?;
                    self.expect_punct(PunctKind::Semicolon)?;
                    return Ok(Stmt::Declaration(ty, id));
                }
            } else if k == KeywordKind::Return {
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
                if let TokenKind::Keyword(k) = next_token.kind.clone() {
                    if k == KeywordKind::Else {
                        self.eat()?;
                        else_stmt = Some(Box::new(self.parse_stmt()?));
                    }
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
            }
        } else if let TokenKind::Identifier(id) = token.kind.clone() {
            self.eat()?;
            if let Ok(t) = self.current_token() {
                if let TokenKind::Punct(p) = t.kind {
                    if p == PunctKind::Colon {
                        self.eat()?;
                        let stmt = self.parse_stmt()?;
                        return Ok(Stmt::Label(id, Box::new(stmt)));
                    }
                }
            }
        }
        Err(ParserError::UnexpectedToken(token))
    }

    fn parse_function(&mut self) -> Result<Function, ParserError> {
        self.expect_keyword(KeywordKind::Int)?;
        self.expect_identifier("main")?;
        self.expect_punct(PunctKind::LeftParen)?;
        self.expect_punct(PunctKind::RightParen)?;
        self.expect_punct(PunctKind::LeftBrace)?;
        let mut stmts = Vec::new();
        while let Ok(t) = self.current_token() {
            if let TokenKind::Punct(p) = t.kind {
                if p == PunctKind::RightBrace {
                    self.eat()?;
                    break;
                }
            }
            stmts.push(self.parse_stmt()?);
        }
        Ok(Function {
            name: "main".to_string(),
            body: stmts,
        })
    }

    pub fn parse(&mut self) -> Result<Program, ParserError> {
        let function = self.parse_function()?;
        Ok(Program { function })
    }
}
