use crate::pp::pp_lexer::{PPToken, PPTokenKind};
use crate::pp::preprocessor::PreprocessorError;
use crate::pp::Preprocessor;
use crate::ast::{BinaryOp, UnaryOp};
use symbol_table::GlobalSymbol as Symbol;

#[derive(Debug)]
pub enum PPExpr {
    Number(i64),
    Identifier(String),
    Defined(Box<PPExpr>),
    Binary(BinaryOp, Box<PPExpr>, Box<PPExpr>),
    Unary(UnaryOp, Box<PPExpr>),
    Conditional(Box<PPExpr>, Box<PPExpr>, Box<PPExpr>),
}



impl PPExpr {
    pub fn evaluate(&self, pp: &Preprocessor) -> Result<i64, PreprocessorError> {
        match self {
            PPExpr::Number(n) => Ok(*n),
            PPExpr::Identifier(s) => Ok(if pp.is_macro_defined(&Symbol::new(s)) { 1 } else { 0 }),
            PPExpr::Defined(ident) => {
                if let PPExpr::Identifier(s) = &**ident {
                    Ok(if pp.is_macro_defined(&Symbol::new(s)) { 1 } else { 0 })
                } else {
                    Err(PreprocessorError::InvalidConditionalExpression)
                }
            }
            PPExpr::Binary(op, left, right) => {
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
                            BinaryOp::BitOr => Ok(l | r),
                            BinaryOp::BitXor => Ok(l ^ r),
                            BinaryOp::BitAnd => Ok(l & r),
                            BinaryOp::Equal => Ok(if l == r { 1 } else { 0 }),
                            BinaryOp::NotEqual => Ok(if l != r { 1 } else { 0 }),
                            BinaryOp::Less => Ok(if l < r { 1 } else { 0 }),
                            BinaryOp::LessEqual => Ok(if l <= r { 1 } else { 0 }),
                            BinaryOp::Greater => Ok(if l > r { 1 } else { 0 }),
                            BinaryOp::GreaterEqual => Ok(if l >= r { 1 } else { 0 }),
                            BinaryOp::LShift => Ok(l << r),
                            BinaryOp::RShift => Ok(((l as u64) >> r) as i64),
                            BinaryOp::Add => Ok(l + r),
                            BinaryOp::Sub => Ok(l - r),
                            BinaryOp::Mul => Ok(l * r),
                            BinaryOp::Div => {
                                if r == 0 {
                                    Err(PreprocessorError::InvalidConditionalExpression)
                                } else {
                                    Ok(l / r)
                                }
                            }
                            BinaryOp::Mod => {
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
            PPExpr::Unary(op, operand) => {
                let o = operand.evaluate(pp)?;
                match op {
                    UnaryOp::Plus => Ok(o),
                    UnaryOp::Minus => Ok(-o),
                    UnaryOp::BitNot => Ok(!o),
                    UnaryOp::LogicNot => Ok(if o != 0 { 0 } else { 1 }),
                    _ => unreachable!("Unsupported unary operator in preprocessor"),
                }
            }
            PPExpr::Conditional(cond, true_e, false_e) => {
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

/// Expression interpreter for preprocessor arithmetic
pub struct Interpreter<'a> {
    tokens: &'a [PPToken],
    pos: usize,
    #[allow(dead_code)]
    preprocessor: &'a Preprocessor<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new(tokens: &'a [PPToken], preprocessor: &'a Preprocessor<'a>) -> Self {
        Interpreter {
            tokens,
            pos: 0,
            preprocessor,
        }
    }

    pub fn parse_expression(&mut self) -> Result<PPExpr, PreprocessorError> {
        self.parse_conditional()
    }

    fn parse_conditional(&mut self) -> Result<PPExpr, PreprocessorError> {
        let cond = self.parse_or()?;
        if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Question) {
            self.pos += 1; // consume ?
            let true_e = self.parse_conditional()?; // allow nesting
            if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Colon) {
                self.pos += 1; // consume :
                let false_e = self.parse_conditional()?;
                Ok(PPExpr::Conditional(Box::new(cond), Box::new(true_e), Box::new(false_e)))
            } else {
                Err(PreprocessorError::InvalidConditionalExpression)
            }
        } else {
            Ok(cond)
        }
    }

    fn parse_or(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicOr) {
            self.pos += 1;
            let right = self.parse_and()?;
            left = PPExpr::Binary(BinaryOp::LogicOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_bitwise_or()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicAnd) {
            self.pos += 1;
            let right = self.parse_bitwise_or()?;
            left = PPExpr::Binary(BinaryOp::LogicAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_bitwise_xor()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Or) {
            self.pos += 1;
            let right = self.parse_bitwise_xor()?;
            left = PPExpr::Binary(BinaryOp::BitOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_bitwise_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Xor) {
            self.pos += 1;
            let right = self.parse_bitwise_and()?;
            left = PPExpr::Binary(BinaryOp::BitXor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_equality()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::And) {
            self.pos += 1;
            let right = self.parse_equality()?;
            left = PPExpr::Binary(BinaryOp::BitAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<PPExpr, PreprocessorError> {
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
                left = PPExpr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_relational(&mut self) -> Result<PPExpr, PreprocessorError> {
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
                left = PPExpr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_additive()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::LeftShift | PPTokenKind::RightShift) {
                self.pos += 1;
                let right = self.parse_additive()?;
                let bin_op = match op {
                    PPTokenKind::LeftShift => BinaryOp::LShift,
                    PPTokenKind::RightShift => BinaryOp::RShift,
                    _ => unreachable!(),
                };
                left = PPExpr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_multiplicative()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Plus | PPTokenKind::Minus) {
                self.pos += 1;
                let right = self.parse_multiplicative()?;
                let bin_op = match op {
                    PPTokenKind::Plus => BinaryOp::Add,
                    PPTokenKind::Minus => BinaryOp::Sub,
                    _ => unreachable!(),
                };
                left = PPExpr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<PPExpr, PreprocessorError> {
        let mut left = self.parse_unary()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Star | PPTokenKind::Slash | PPTokenKind::Percent) {
                self.pos += 1;
                let right = self.parse_unary()?;
                let bin_op = match op {
                    PPTokenKind::Star => BinaryOp::Mul,
                    PPTokenKind::Slash => BinaryOp::Div,
                    PPTokenKind::Percent => BinaryOp::Mod,
                    _ => unreachable!(),
                };
                left = PPExpr::Binary(bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<PPExpr, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.defined_symbol()) {
            self.pos += 1;
            let ident = if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LeftParen) {
                self.pos += 1;
                let ident = self.parse_primary()?;
                if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::RightParen) {
                    self.pos += 1;
                    ident
                } else {
                    return Err(PreprocessorError::InvalidConditionalExpression);
                }
            } else {
                self.parse_primary()?
            };
            Ok(PPExpr::Defined(Box::new(ident)))
        } else if matches!(token.kind, PPTokenKind::Plus | PPTokenKind::Minus | PPTokenKind::Tilde | PPTokenKind::Not) {
            self.pos += 1;
            let operand = self.parse_unary()?;
            let unary_op = match token.kind {
                PPTokenKind::Plus => UnaryOp::Plus,
                PPTokenKind::Minus => UnaryOp::Minus,
                PPTokenKind::Tilde => UnaryOp::BitNot,
                PPTokenKind::Not => UnaryOp::LogicNot,
                _ => unreachable!(),
            };
            Ok(PPExpr::Unary(unary_op, Box::new(operand)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<PPExpr, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        self.pos += 1;
        match &token.kind {
            PPTokenKind::Number(sym) => {
                let text = sym.as_str();
                // Strip suffixes: u U l L ll LL (case insensitive)
                let mut num_text = text;
                let lower = text.to_lowercase();
                if lower.ends_with("ull") || lower.ends_with("llu") {
                    num_text = &text[..text.len() - 3];
                } else if lower.ends_with("ul") || lower.ends_with("lu") || lower.ends_with("ll") {
                    num_text = &text[..text.len() - 2];
                } else if lower.ends_with("u") || lower.ends_with("l") {
                    num_text = &text[..text.len() - 1];
                }
                // Parse as i64, handle hex, octal, decimal
                let num = if num_text.starts_with("0x") || num_text.starts_with("0X") {
                    i64::from_str_radix(&num_text[2..], 16)
                } else if num_text.starts_with("0") && num_text.len() > 1 {
                    i64::from_str_radix(num_text, 8)
                } else {
                    num_text.parse::<i64>()
                }.map_err(|_| PreprocessorError::InvalidConditionalExpression)?;
                Ok(PPExpr::Number(num))
            }
            PPTokenKind::CharLiteral(codepoint, _) => {
                Ok(PPExpr::Number(*codepoint as i64))
            }
            PPTokenKind::Identifier(sym) => {
                // Identifiers are 0 if not defined, but since we expanded macros, should be numbers
                Ok(PPExpr::Identifier(sym.as_str().to_string()))
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