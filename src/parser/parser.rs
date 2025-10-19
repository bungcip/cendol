use crate::parser::ast::{Expr, Function, Program, Stmt};
use crate::parser::error::ParserError;
use crate::preprocessor::token::{Token, TokenKind};

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

    fn expect_punct(&mut self, value: &str) -> Result<(), ParserError> {
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

    fn expect_keyword(&mut self, value: &str) -> Result<(), ParserError> {
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
        self.expect_keyword("return")?;
        let expr = self.parse_expr()?;
        self.expect_punct(";")?;
        Ok(Stmt::Return(expr))
    }

    fn parse_function(&mut self) -> Result<Function, ParserError> {
        self.expect_keyword("int")?;
        self.expect_identifier("main")?;
        self.expect_punct("(")?;
        self.expect_punct(")")?;
        self.expect_punct("{")?;
        let body = self.parse_stmt()?;
        self.expect_punct("}")?;
        Ok(Function {
            name: "main".to_string(),
            body,
        })
    }

    pub fn parse(&mut self) -> Result<Program, ParserError> {
        let function = self.parse_function()?;
        Ok(Program { function })
    }
}
