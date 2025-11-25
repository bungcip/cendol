use crate::pp::pp_lexer::{PPToken, PPTokenKind};
use crate::pp::preprocessor::PreprocessorError;
use crate::pp::Preprocessor;
use symbol_table::GlobalSymbol as Symbol;

#[derive(Debug)]
pub enum Expr {
    Number(i64),
    Identifier(String),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Conditional(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum BinaryOp {
    LogicOr,
    LogicAnd,
    Or,
    Xor,
    And,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    LeftShift,
    RightShift,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
}

#[derive(Debug)]
pub enum UnaryOp {
    Plus,
    Minus,
    Tilde,
    Not,
}

impl Expr {
    pub fn evaluate(&self, pp: &Preprocessor) -> Result<i64, PreprocessorError> {
        match self {
            Expr::Number(n) => Ok(*n),
            Expr::Identifier(s) => Ok(if pp.is_macro_defined(&Symbol::new(s)) { 1 } else { 0 }),
            Expr::Binary(op, left, right) => {
                let l = left.evaluate(pp)?;
                match op {
                    BinaryOp::LogicAnd => {
                        if l == 0 {
                            Ok(0)
                        } else {
                            let r = right.evaluate(pp)?;
                            Ok(if l != 0 && r != 0 { 1 } else { 0 })
                        }
                    }
                    BinaryOp::LogicOr => {
                        if l != 0 {
                            Ok(1)
                        } else {
                            let r = right.evaluate(pp)?;
                            Ok(if l != 0 || r != 0 { 1 } else { 0 })
                        }
                    }
                    _ => {
                        let r = right.evaluate(pp)?;
                        match op {
                            BinaryOp::Or => Ok(l | r),
                            BinaryOp::Xor => Ok(l ^ r),
                            BinaryOp::And => Ok(l & r),
                            BinaryOp::Equal => Ok(if l == r { 1 } else { 0 }),
                            BinaryOp::NotEqual => Ok(if l != r { 1 } else { 0 }),
                            BinaryOp::Less => Ok(if l < r { 1 } else { 0 }),
                            BinaryOp::LessEqual => Ok(if l <= r { 1 } else { 0 }),
                            BinaryOp::Greater => Ok(if l > r { 1 } else { 0 }),
                            BinaryOp::GreaterEqual => Ok(if l >= r { 1 } else { 0 }),
                            BinaryOp::LeftShift => Ok(l << r),
                            BinaryOp::RightShift => Ok(((l as u64) >> r) as i64),
                            BinaryOp::Plus => Ok(l + r),
                            BinaryOp::Minus => Ok(l - r),
                            BinaryOp::Star => Ok(l * r),
                            BinaryOp::Slash => {
                                if r == 0 {
                                    Err(PreprocessorError::InvalidConditionalExpression)
                                } else {
                                    Ok(l / r)
                                }
                            }
                            BinaryOp::Percent => {
                                if r == 0 {
                                    Err(PreprocessorError::InvalidConditionalExpression)
                                } else {
                                    Ok(l % r)
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
            Expr::Unary(op, operand) => {
                let o = operand.evaluate(pp)?;
                match op {
                    UnaryOp::Plus => Ok(o),
                    UnaryOp::Minus => Ok(-o),
                    UnaryOp::Tilde => Ok(!o),
                    UnaryOp::Not => Ok(if o != 0 { 0 } else { 1 }),
                }
            }
            Expr::Conditional(cond, true_e, false_e) => {
                let c = cond.evaluate(pp)?;
                if c != 0 {
                    true_e.evaluate(pp)
                } else {
                    false_e.evaluate(pp)
                }
            }
        }
    }
}

/// Expression parser for preprocessor arithmetic
pub struct ExpressionParser<'a> {
    tokens: &'a [PPToken],
    pos: usize,
    preprocessor: &'a Preprocessor<'a>,
}

impl<'a> ExpressionParser<'a> {
    pub fn new(tokens: &'a [PPToken], preprocessor: &'a Preprocessor<'a>) -> Self {
        ExpressionParser {
            tokens,
            pos: 0,
            preprocessor,
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, PreprocessorError> {
        self.parse_conditional()
    }

    fn parse_conditional(&mut self) -> Result<Expr, PreprocessorError> {
        let cond = self.parse_or()?;
        if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Question) {
            self.pos += 1; // consume ?
            let true_e = self.parse_conditional()?; // allow nesting
            if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Colon) {
                self.pos += 1; // consume :
                let false_e = self.parse_conditional()?;
                Ok(Expr::Conditional(Box::new(cond), Box::new(true_e), Box::new(false_e)))
            } else {
                Err(PreprocessorError::InvalidConditionalExpression)
            }
        } else {
            Ok(cond)
        }
    }

    fn parse_or(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicOr) {
            self.pos += 1;
            let right = self.parse_and()?;
            left = Expr::Binary(BinaryOp::LogicOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_bitwise_or()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicAnd) {
            self.pos += 1;
            let right = self.parse_bitwise_or()?;
            left = Expr::Binary(BinaryOp::LogicAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_bitwise_xor()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Or) {
            self.pos += 1;
            let right = self.parse_bitwise_xor()?;
            left = Expr::Binary(BinaryOp::Or, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_bitwise_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Xor) {
            self.pos += 1;
            let right = self.parse_bitwise_and()?;
            left = Expr::Binary(BinaryOp::Xor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_equality()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::And) {
            self.pos += 1;
            let right = self.parse_equality()?;
            left = Expr::Binary(BinaryOp::And, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_relational()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Equal | PPTokenKind::NotEqual) {
                self.pos += 1;
                let right = self.parse_relational()?;
                let bin_op = match op {
                    PPTokenKind::Equal => BinaryOp::Equal,
                    PPTokenKind::NotEqual => BinaryOp::NotEqual,
                    _ => unreachable!(),
                };
                left = Expr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_relational(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_shift()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Less | PPTokenKind::LessEqual | PPTokenKind::Greater | PPTokenKind::GreaterEqual) {
                self.pos += 1;
                let right = self.parse_shift()?;
                let bin_op = match op {
                    PPTokenKind::Less => BinaryOp::Less,
                    PPTokenKind::LessEqual => BinaryOp::LessEqual,
                    PPTokenKind::Greater => BinaryOp::Greater,
                    PPTokenKind::GreaterEqual => BinaryOp::GreaterEqual,
                    _ => unreachable!(),
                };
                left = Expr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_additive()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::LeftShift | PPTokenKind::RightShift) {
                self.pos += 1;
                let right = self.parse_additive()?;
                let bin_op = match op {
                    PPTokenKind::LeftShift => BinaryOp::LeftShift,
                    PPTokenKind::RightShift => BinaryOp::RightShift,
                    _ => unreachable!(),
                };
                left = Expr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_multiplicative()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Plus | PPTokenKind::Minus) {
                self.pos += 1;
                let right = self.parse_multiplicative()?;
                let bin_op = match op {
                    PPTokenKind::Plus => BinaryOp::Plus,
                    PPTokenKind::Minus => BinaryOp::Minus,
                    _ => unreachable!(),
                };
                left = Expr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, PreprocessorError> {
        let mut left = self.parse_unary()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Star | PPTokenKind::Slash | PPTokenKind::Percent) {
                self.pos += 1;
                let right = self.parse_unary()?;
                let bin_op = match op {
                    PPTokenKind::Star => BinaryOp::Star,
                    PPTokenKind::Slash => BinaryOp::Slash,
                    PPTokenKind::Percent => BinaryOp::Percent,
                    _ => unreachable!(),
                };
                left = Expr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let op = &self.tokens[self.pos].kind;
        if matches!(op, PPTokenKind::Plus | PPTokenKind::Minus | PPTokenKind::Tilde | PPTokenKind::Not) {
            self.pos += 1;
            let operand = self.parse_unary()?;
            let unary_op = match op {
                PPTokenKind::Plus => UnaryOp::Plus,
                PPTokenKind::Minus => UnaryOp::Minus,
                PPTokenKind::Tilde => UnaryOp::Tilde,
                PPTokenKind::Not => UnaryOp::Not,
                _ => unreachable!(),
            };
            Ok(Expr::Unary(unary_op, Box::new(operand)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        self.pos += 1;
        match &token.kind {
            PPTokenKind::Number(sym) => {
                let text = sym.as_str();
                // Parse as i64, handle hex, octal, decimal
                let num = if text.starts_with("0x") || text.starts_with("0X") {
                    i64::from_str_radix(&text[2..], 16)
                } else if text.starts_with("0") && text.len() > 1 {
                    i64::from_str_radix(text, 8)
                } else {
                    text.parse::<i64>()
                }.map_err(|_| PreprocessorError::InvalidConditionalExpression)?;
                Ok(Expr::Number(num))
            }
            PPTokenKind::Identifier(sym) => {
                // Identifiers are 0 if not defined, but since we expanded macros, should be numbers
                Ok(Expr::Identifier(sym.as_str().to_string()))
            }
            PPTokenKind::LeftParen => {
                let result = self.parse_expression()?;
                if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::RightParen) {
                    self.pos += 1;
                    Ok(result)
                } else {
                    Err(PreprocessorError::InvalidConditionalExpression)
                }
            }
            _ => Err(PreprocessorError::InvalidConditionalExpression),
        }
    }
}