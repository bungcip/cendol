use crate::pp::pp_lexer::{PPToken, PPTokenKind};
use crate::pp::preprocessor::PreprocessorError;
use crate::pp::Preprocessor;

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

    pub fn parse_expression(&mut self) -> Result<i64, PreprocessorError> {
        self.parse_conditional()
    }

    fn parse_conditional(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_or()?;
        if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Question) {
            self.pos += 1; // consume ?
            let true_val = self.parse_conditional()?; // allow nesting
            if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Colon) {
                self.pos += 1; // consume :
                let false_val = self.parse_conditional()?;
                left = if left != 0 { true_val } else { false_val };
            } else {
                return Err(PreprocessorError::InvalidConditionalExpression);
            }
        }
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicOr) {
            self.pos += 1;
            let right = self.parse_and()?;
            left = if left != 0 || right != 0 { 1 } else { 0 };
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_bitwise_or()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicAnd) {
            self.pos += 1;
            let right = self.parse_bitwise_or()?;
            left = if left != 0 && right != 0 { 1 } else { 0 };
        }
        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_bitwise_xor()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Or) {
            self.pos += 1;
            let right = self.parse_bitwise_xor()?;
            left |= right;
        }
        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_bitwise_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Xor) {
            self.pos += 1;
            let right = self.parse_bitwise_and()?;
            left ^= right;
        }
        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_equality()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::And) {
            self.pos += 1;
            let right = self.parse_equality()?;
            left &= right;
        }
        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_relational()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Equal | PPTokenKind::NotEqual) {
                self.pos += 1;
                let right = self.parse_relational()?;
                left = match op {
                    PPTokenKind::Equal => if left == right { 1 } else { 0 },
                    PPTokenKind::NotEqual => if left != right { 1 } else { 0 },
                    _ => unreachable!(),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_relational(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_shift()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Less | PPTokenKind::LessEqual | PPTokenKind::Greater | PPTokenKind::GreaterEqual) {
                self.pos += 1;
                let right = self.parse_shift()?;
                left = match op {
                    PPTokenKind::Less => if left < right { 1 } else { 0 },
                    PPTokenKind::LessEqual => if left <= right { 1 } else { 0 },
                    PPTokenKind::Greater => if left > right { 1 } else { 0 },
                    PPTokenKind::GreaterEqual => if left >= right { 1 } else { 0 },
                    _ => unreachable!(),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_additive()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::LeftShift | PPTokenKind::RightShift) {
                self.pos += 1;
                let right = self.parse_additive()?;
                left = match op {
                    PPTokenKind::LeftShift => left << right,
                    PPTokenKind::RightShift => ((left as u64) >> right) as i64,
                    _ => unreachable!(),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_multiplicative()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Plus | PPTokenKind::Minus) {
                self.pos += 1;
                let right = self.parse_multiplicative()?;
                left = match op {
                    PPTokenKind::Plus => left + right,
                    PPTokenKind::Minus => left - right,
                    _ => unreachable!(),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<i64, PreprocessorError> {
        let mut left = self.parse_unary()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(op, PPTokenKind::Star | PPTokenKind::Slash | PPTokenKind::Percent) {
                self.pos += 1;
                let right = self.parse_unary()?;
                left = match op {
                    PPTokenKind::Star => left * right,
                    PPTokenKind::Slash => {
                        if right == 0 {
                            return Err(PreprocessorError::InvalidConditionalExpression);
                        }
                        left / right
                    },
                    PPTokenKind::Percent => {
                        if right == 0 {
                            return Err(PreprocessorError::InvalidConditionalExpression);
                        }
                        left % right
                    },
                    _ => unreachable!(),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<i64, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let op = &self.tokens[self.pos].kind;
        if matches!(op, PPTokenKind::Plus | PPTokenKind::Minus | PPTokenKind::Tilde | PPTokenKind::Not) {
            self.pos += 1;
            let operand = self.parse_unary()?;
            match op {
                PPTokenKind::Plus => Ok(operand),
                PPTokenKind::Minus => Ok(-operand),
                PPTokenKind::Tilde => Ok(!operand),
                PPTokenKind::Not => Ok(if operand != 0 { 0 } else { 1 }),
                _ => unreachable!(),
            }
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<i64, PreprocessorError> {
        if self.pos >= self.tokens.len() {
            return Err(PreprocessorError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        self.pos += 1;
        match &token.kind {
            PPTokenKind::Number(sym) => {
                let text = sym.as_str();
                // Parse as i64, handle hex, octal, decimal
                if text.starts_with("0x") || text.starts_with("0X") {
                    i64::from_str_radix(&text[2..], 16)
                } else if text.starts_with("0") && text.len() > 1 {
                    i64::from_str_radix(text, 8)
                } else {
                    text.parse::<i64>()
                }.map_err(|_| PreprocessorError::InvalidConditionalExpression)
            }
            PPTokenKind::Identifier(sym) => {
                // Identifiers are 0 if not defined, but since we expanded macros, should be numbers
                Ok(if self.preprocessor.is_macro_defined(sym) { 1 } else { 0 })
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