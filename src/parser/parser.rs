use crate::preprocessor::token::{Token, TokenKind};
use crate::parser::ast::Expr;
use crate::parser::error::ParserError;

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

    fn factor(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind {
            TokenKind::Number(n) => {
                self.eat()?;
                Ok(Expr::Number(n.parse().unwrap()))
            }
            _ => Err(ParserError::UnexpectedToken(token)),
        }
    }

    fn term(&mut self) -> Result<Expr, ParserError> {
        let mut node = self.factor()?;

        loop {
            match self.current_token() {
                Ok(token) => match token.kind {
                    TokenKind::Punct(p) if p == "*" => {
                        self.eat()?;
                        node = Expr::Mul(Box::new(node), Box::new(self.factor()?));
                    }
                    TokenKind::Punct(p) if p == "/" => {
                        self.eat()?;
                        node = Expr::Div(Box::new(node), Box::new(self.factor()?));
                    }
                    _ => break,
                },
                Err(ParserError::UnexpectedEof) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(node)
    }

    pub fn expr(&mut self) -> Result<Expr, ParserError> {
        let mut node = self.term()?;

        loop {
            match self.current_token() {
                Ok(token) => match token.kind {
                    TokenKind::Punct(p) if p == "+" => {
                        self.eat()?;
                        node = Expr::Add(Box::new(node), Box::new(self.term()?));
                    }
                    TokenKind::Punct(p) if p == "-" => {
                        self.eat()?;
                        node = Expr::Sub(Box::new(node), Box::new(self.term()?));
                    }
                    _ => break,
                },
                Err(ParserError::UnexpectedEof) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(node)
    }
}
