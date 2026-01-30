use crate::ast::literal::IntegerSuffix;
use crate::ast::literal_parsing;
use crate::ast::{BinaryOp, UnaryOp};
use crate::intern::StringId;
use crate::pp::{PPError, PPToken, PPTokenKind, Preprocessor};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExprValue {
    pub value: u64,
    pub is_unsigned: bool,
}

impl ExprValue {
    pub(crate) fn new(value: u64, is_unsigned: bool) -> Self {
        ExprValue { value, is_unsigned }
    }

    fn from_bool(b: bool) -> Self {
        ExprValue {
            value: if b { 1 } else { 0 },
            is_unsigned: false, // Logical results are signed int (0 or 1)
        }
    }

    pub(crate) fn is_truthy(&self) -> bool {
        self.value != 0
    }
}

#[derive(Debug)]
pub(crate) enum PPExpr {
    Number(ExprValue),
    Identifier(String),
    Defined(Box<PPExpr>),
    HasInclude(String, bool), // (path, is_angled)
    Binary(BinaryOp, Box<PPExpr>, Box<PPExpr>),
    Unary(UnaryOp, Box<PPExpr>),
    Conditional(Box<PPExpr>, Box<PPExpr>, Box<PPExpr>),
}

impl PPExpr {
    pub(crate) fn evaluate(&self, pp: &Preprocessor) -> Result<ExprValue, PPError> {
        match self {
            PPExpr::Number(n) => Ok(*n),
            PPExpr::Identifier(_s) => Ok(ExprValue::new(0, false)), // C11 6.10.1p4: All remaining identifiers are replaced with 0
            PPExpr::Defined(ident) => {
                if let PPExpr::Identifier(s) = &**ident {
                    let defined = pp.is_macro_defined(&StringId::new(s));
                    Ok(ExprValue::from_bool(defined))
                } else {
                    Err(PPError::InvalidConditionalExpression)
                }
            }
            PPExpr::HasInclude(path, is_angled) => {
                let exists = pp.check_header_exists(path, *is_angled);
                Ok(ExprValue::from_bool(exists))
            }
            PPExpr::Binary(op, left, right) => {
                let l = left.evaluate(pp)?;
                match op {
                    BinaryOp::LogicAnd => {
                        if !l.is_truthy() {
                            Ok(ExprValue::from_bool(false))
                        } else {
                            let r = right.evaluate(pp)?;
                            Ok(ExprValue::from_bool(r.is_truthy()))
                        }
                    }
                    BinaryOp::LogicOr => {
                        if l.is_truthy() {
                            Ok(ExprValue::from_bool(true))
                        } else {
                            let r = right.evaluate(pp)?;
                            Ok(ExprValue::from_bool(r.is_truthy()))
                        }
                    }
                    _ => {
                        let r = right.evaluate(pp)?;
                        // Usual arithmetic conversions
                        let is_unsigned = l.is_unsigned || r.is_unsigned;
                        let l_val = l.value;
                        let r_val = r.value;

                        match op {
                            BinaryOp::BitOr => Ok(ExprValue::new(l_val | r_val, is_unsigned)),
                            BinaryOp::BitXor => Ok(ExprValue::new(l_val ^ r_val, is_unsigned)),
                            BinaryOp::BitAnd => Ok(ExprValue::new(l_val & r_val, is_unsigned)),
                            BinaryOp::Equal => Ok(ExprValue::from_bool(l_val == r_val)),
                            BinaryOp::NotEqual => Ok(ExprValue::from_bool(l_val != r_val)),
                            BinaryOp::Less => {
                                if is_unsigned {
                                    Ok(ExprValue::from_bool(l_val < r_val))
                                } else {
                                    Ok(ExprValue::from_bool((l_val as i64) < (r_val as i64)))
                                }
                            }
                            BinaryOp::LessEqual => {
                                if is_unsigned {
                                    Ok(ExprValue::from_bool(l_val <= r_val))
                                } else {
                                    Ok(ExprValue::from_bool((l_val as i64) <= (r_val as i64)))
                                }
                            }
                            BinaryOp::Greater => {
                                if is_unsigned {
                                    Ok(ExprValue::from_bool(l_val > r_val))
                                } else {
                                    Ok(ExprValue::from_bool((l_val as i64) > (r_val as i64)))
                                }
                            }
                            BinaryOp::GreaterEqual => {
                                if is_unsigned {
                                    Ok(ExprValue::from_bool(l_val >= r_val))
                                } else {
                                    Ok(ExprValue::from_bool((l_val as i64) >= (r_val as i64)))
                                }
                            }
                            BinaryOp::LShift => {
                                // Shift count is not subject to usual arithmetic conversions for type
                                // But the result type is that of the promoted LHS.
                                // We'll just use the promoted LHS type (integer promotion, but here we are already 64-bit).
                                // C11: "The result has the type of the left operand."
                                // So we preserve l.is_unsigned.
                                let shift_amount = r_val as u32;
                                // Handle shift >= 64 behavior (UB in C, wrap in Rust)
                                if shift_amount >= 64 {
                                    // UB, but zeroing is a common safe behavior or wrapping.
                                    // Rust panics in debug on overflow, wrapping_shl masks.
                                    Ok(ExprValue::new(l_val.wrapping_shl(shift_amount), l.is_unsigned))
                                } else {
                                    Ok(ExprValue::new(l_val << shift_amount, l.is_unsigned))
                                }
                            }
                            BinaryOp::RShift => {
                                let shift_amount = r_val as u32;
                                if shift_amount >= 64 {
                                    // UB
                                    Ok(ExprValue::new(l_val.wrapping_shr(shift_amount), l.is_unsigned))
                                } else if l.is_unsigned {
                                    // Logical shift
                                    Ok(ExprValue::new(l_val >> shift_amount, true))
                                } else {
                                    // Arithmetic shift
                                    Ok(ExprValue::new(((l_val as i64) >> shift_amount) as u64, false))
                                }
                            }
                            BinaryOp::Add => Ok(ExprValue::new(l_val.wrapping_add(r_val), is_unsigned)),
                            BinaryOp::Sub => Ok(ExprValue::new(l_val.wrapping_sub(r_val), is_unsigned)),
                            BinaryOp::Mul => Ok(ExprValue::new(l_val.wrapping_mul(r_val), is_unsigned)),
                            BinaryOp::Div => {
                                if r_val == 0 {
                                    Err(PPError::InvalidConditionalExpression)
                                } else if is_unsigned {
                                    Ok(ExprValue::new(l_val / r_val, true))
                                } else {
                                    // Signed division
                                    // Check for overflow: MIN / -1
                                    let l_signed = l_val as i64;
                                    let r_signed = r_val as i64;
                                    if l_signed == i64::MIN && r_signed == -1 {
                                        Ok(ExprValue::new(l_signed as u64, false)) // or overflow behavior
                                    } else {
                                        Ok(ExprValue::new((l_signed / r_signed) as u64, false))
                                    }
                                }
                            }
                            BinaryOp::Mod => {
                                if r_val == 0 {
                                    Err(PPError::InvalidConditionalExpression)
                                } else if is_unsigned {
                                    Ok(ExprValue::new(l_val % r_val, true))
                                } else {
                                    let l_signed = l_val as i64;
                                    let r_signed = r_val as i64;
                                    if l_signed == i64::MIN && r_signed == -1 {
                                        Ok(ExprValue::new(0, false))
                                    } else {
                                        Ok(ExprValue::new((l_signed % r_signed) as u64, false))
                                    }
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
                    UnaryOp::Minus => {
                        // Unsigned negation is 2's complement (wrapping_neg)
                        Ok(ExprValue::new(o.value.wrapping_neg(), o.is_unsigned))
                    }
                    UnaryOp::BitNot => Ok(ExprValue::new(!o.value, o.is_unsigned)),
                    UnaryOp::LogicNot => Ok(ExprValue::from_bool(!o.is_truthy())),
                    _ => unreachable!("Unsupported unary operator in preprocessor"),
                }
            }
            PPExpr::Conditional(cond, true_e, false_e) => {
                let c = cond.evaluate(pp)?;
                let t = true_e.evaluate(pp)?;
                let f = false_e.evaluate(pp)?;

                if c.is_truthy() {
                    // Result type depends on both operands usual arithmetic conversions
                    // But we only return the evaluated one.
                    // However, C11 says "the other operand is evaluated ... The result has the type..."
                    // In an interpreter, we just return the value.
                    // But if we wanted to be pedantic about type of the expression (e.g. for `sizeof`),
                    // we would need to merge types.
                    // But here we just return the value.
                    // Wait, if I have `1 ? -1 : 0U`. Result should be unsigned.
                    // `-1` converted to unsigned is MAX.
                    // If we return `-1` as signed, and later compare it...
                    // "The second and third operands are converted ... to the common type."
                    let is_unsigned = t.is_unsigned || f.is_unsigned;
                    if is_unsigned {
                        Ok(ExprValue::new(t.value, true))
                    } else {
                        Ok(t)
                    }
                } else {
                    let is_unsigned = t.is_unsigned || f.is_unsigned;
                    if is_unsigned {
                        Ok(ExprValue::new(f.value, true))
                    } else {
                        Ok(f)
                    }
                }
            }
        }
    }
}

/// Expression interpreter for preprocessor arithmetic
pub(crate) struct Interpreter<'a> {
    tokens: &'a [PPToken],
    pos: usize,
    preprocessor: &'a Preprocessor<'a>,
}

impl<'a> Interpreter<'a> {
    pub(crate) fn new(tokens: &'a [PPToken], preprocessor: &'a Preprocessor<'a>) -> Self {
        Interpreter {
            tokens,
            pos: 0,
            preprocessor,
        }
    }

    pub(crate) fn evaluate(&mut self) -> Result<ExprValue, PPError> {
        let expr = self.parse_conditional()?;
        expr.evaluate(self.preprocessor)
    }

    fn parse_conditional(&mut self) -> Result<PPExpr, PPError> {
        let cond = self.parse_or()?;
        if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Question) {
            self.pos += 1; // consume ?
            let true_e = self.parse_conditional()?; // allow nesting
            if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Colon) {
                self.pos += 1; // consume :
                let false_e = self.parse_conditional()?;
                Ok(PPExpr::Conditional(Box::new(cond), Box::new(true_e), Box::new(false_e)))
            } else {
                Err(PPError::InvalidConditionalExpression)
            }
        } else {
            Ok(cond)
        }
    }

    fn parse_or(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicOr) {
            self.pos += 1;
            let right = self.parse_and()?;
            left = PPExpr::Binary(BinaryOp::LogicOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_bitwise_or()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LogicAnd) {
            self.pos += 1;
            let right = self.parse_bitwise_or()?;
            left = PPExpr::Binary(BinaryOp::LogicAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_bitwise_xor()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Or) {
            self.pos += 1;
            let right = self.parse_bitwise_xor()?;
            left = PPExpr::Binary(BinaryOp::BitOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_bitwise_and()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::Xor) {
            self.pos += 1;
            let right = self.parse_bitwise_and()?;
            left = PPExpr::Binary(BinaryOp::BitXor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_equality()?;
        while self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::And) {
            self.pos += 1;
            let right = self.parse_equality()?;
            left = PPExpr::Binary(BinaryOp::BitAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<PPExpr, PPError> {
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

    fn parse_relational(&mut self) -> Result<PPExpr, PPError> {
        let mut left = self.parse_shift()?;
        while self.pos < self.tokens.len() {
            let op = &self.tokens[self.pos].kind;
            if matches!(
                op,
                PPTokenKind::Less | PPTokenKind::LessEqual | PPTokenKind::Greater | PPTokenKind::GreaterEqual
            ) {
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

    fn parse_shift(&mut self) -> Result<PPExpr, PPError> {
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

    fn parse_additive(&mut self) -> Result<PPExpr, PPError> {
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

    fn parse_multiplicative(&mut self) -> Result<PPExpr, PPError> {
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

    fn parse_unary(&mut self) -> Result<PPExpr, PPError> {
        if self.pos >= self.tokens.len() {
            return Err(PPError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.defined_symbol()) {
            self.pos += 1;
            let ident = if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::LeftParen)
            {
                self.pos += 1;
                let ident = self.parse_primary()?;
                if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::RightParen) {
                    self.pos += 1;
                    ident
                } else {
                    return Err(PPError::InvalidConditionalExpression);
                }
            } else {
                self.parse_primary()?
            };
            Ok(PPExpr::Defined(Box::new(ident)))
        } else if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.has_include_symbol()) {
            self.pos += 1; // consume __has_include

            // Expect LeftParen
            if self.pos >= self.tokens.len() || self.tokens[self.pos].kind != PPTokenKind::LeftParen {
                return Err(PPError::InvalidConditionalExpression);
            }
            self.pos += 1;

            // Parse argument
            if self.pos >= self.tokens.len() {
                return Err(PPError::InvalidConditionalExpression);
            }

            let (path, is_angled) = match &self.tokens[self.pos].kind {
                PPTokenKind::StringLiteral(sym) => {
                    let full_str = sym.as_str();
                    if full_str.starts_with('"') && full_str.ends_with('"') {
                        self.pos += 1;
                        (full_str[1..full_str.len() - 1].to_string(), false)
                    } else {
                        return Err(PPError::InvalidConditionalExpression);
                    }
                }
                PPTokenKind::Less => {
                    // Angled include
                    self.pos += 1;
                    let mut path_str = String::new();
                    loop {
                        if self.pos >= self.tokens.len() {
                            return Err(PPError::InvalidConditionalExpression);
                        }
                        let token = &self.tokens[self.pos];
                        if token.kind == PPTokenKind::Greater {
                            self.pos += 1;
                            break;
                        }
                        path_str.push_str(self.preprocessor.get_token_text(token));
                        self.pos += 1;
                    }
                    (path_str, true)
                }
                _ => return Err(PPError::InvalidConditionalExpression),
            };

            // Expect RightParen
            if self.pos >= self.tokens.len() || self.tokens[self.pos].kind != PPTokenKind::RightParen {
                return Err(PPError::InvalidConditionalExpression);
            }
            self.pos += 1;

            Ok(PPExpr::HasInclude(path, is_angled))
        } else if matches!(
            token.kind,
            PPTokenKind::Plus | PPTokenKind::Minus | PPTokenKind::Tilde | PPTokenKind::Not
        ) {
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

    fn parse_primary(&mut self) -> Result<PPExpr, PPError> {
        if self.pos >= self.tokens.len() {
            return Err(PPError::InvalidConditionalExpression);
        }
        let token = &self.tokens[self.pos];
        self.pos += 1;
        match &token.kind {
            PPTokenKind::Number(sym) => {
                let text = sym.as_str();
                if let Ok((val, suffix)) = literal_parsing::parse_c11_integer_literal(text) {
                    let mut is_unsigned =
                        matches!(suffix, Some(IntegerSuffix::U | IntegerSuffix::UL | IntegerSuffix::ULL));

                    // C11 6.3.1.1: If it fits in signed i64, it's signed (unless U suffix).
                    // If it doesn't fit in i64, it depends on base.
                    // Hex/Octal: can be unsigned if doesn't fit in signed.
                    // Decimal: technically should be signed long long, but if it overflows, it's UB or implementation defined.
                    // We treat large decimals as unsigned too to support `u64` range fully.
                    let fits_i64 = val <= i64::MAX as u64;

                    if !is_unsigned && !fits_i64 {
                        // Promoted to unsigned if hex/octal or too big
                        // For decimal, ideally we warn, but here we just accept as unsigned to match typical behavior for u64 support
                        is_unsigned = true;
                    }

                    Ok(PPExpr::Number(ExprValue::new(val, is_unsigned)))
                } else {
                    Err(PPError::InvalidConditionalExpression)
                }
            }
            PPTokenKind::CharLiteral(codepoint, _) => Ok(PPExpr::Number(ExprValue::new(*codepoint as u64, false))),
            PPTokenKind::Identifier(sym) => {
                // Identifiers are 0 if not defined, but since we expanded macros, should be numbers
                Ok(PPExpr::Identifier(sym.as_str().to_string()))
            }
            PPTokenKind::LeftParen => {
                let result = self.parse_conditional()?;
                if self.pos < self.tokens.len() && matches!(self.tokens[self.pos].kind, PPTokenKind::RightParen) {
                    self.pos += 1;
                    Ok(result)
                } else {
                    Err(PPError::InvalidConditionalExpression)
                }
            }
            _ => Err(PPError::InvalidConditionalExpression),
        }
    }
}
