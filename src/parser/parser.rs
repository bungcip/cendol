use crate::parser::ast::{Expr, Function, Program, Stmt};
use crate::parser::error::ParserError;
use crate::preprocessor::token::{KeywordKind, PunctKind, Token, TokenKind};

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Result<Self, ParserError> {
        let mut parser = Parser {
            tokens,
            position: 0,
        };
        parser.skip_whitespace()?;
        Ok(parser)
    }

    fn current_token(&self) -> Result<Token, ParserError> {
        self.tokens
            .get(self.position)
            .cloned()
            .ok_or(ParserError::UnexpectedEof)
    }

    fn skip_whitespace(&mut self) -> Result<(), ParserError> {
        while let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::Whitespace(_)) {
                self.position += 1;
            } else {
                break;
            }
        }
        Ok(())
    }

    fn eat(&mut self) -> Result<(), ParserError> {
        self.position += 1;
        self.skip_whitespace()
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
        self.parse_comparison()
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.eat()?;
                Ok(Expr::Number(n.parse().unwrap()))
            }
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
        let body = self.parse_stmt()?;
        self.expect_punct(PunctKind::RightBrace)?;
        Ok(Function {
            name: "main".to_string(),
            body: Box::new(body),
        })
    }

    pub fn parse(&mut self) -> Result<Program, ParserError> {
        let function = self.parse_function()?;
        Ok(Program { function })
    }
}
