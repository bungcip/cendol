use crate::ast::StringId;
use crate::ast::literal::IntegerSuffix;
use crate::ast::literal_parsing;
use crate::ast::{BinaryOp, UnaryOp};
use crate::pp::{PPError, PPErrorKind, PPToken, PPTokenKind, Preprocessor};
use crate::source_manager::{SourceLoc, SourceSpan};

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
            value: u64::from(b),
            is_unsigned: false,
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
    HasInclude(String, bool),
    Binary(BinaryOp, Box<PPExpr>, Box<PPExpr>),
    Unary(UnaryOp, Box<PPExpr>),
    Conditional(Box<PPExpr>, Box<PPExpr>, Box<PPExpr>),
}

impl PPExpr {
    pub(crate) fn evaluate(&self, pp: &Preprocessor, span: SourceSpan) -> Result<ExprValue, PPError> {
        match self {
            PPExpr::Number(n) => Ok(*n),
            PPExpr::Identifier(_) => Ok(ExprValue::new(0, false)), // C11 6.10.1p4: All remaining identifiers are replaced with 0
            PPExpr::Defined(ident) => {
                if let PPExpr::Identifier(s) = &**ident {
                    Ok(ExprValue::from_bool(pp.is_macro_defined(&StringId::new(s))))
                } else {
                    Err(Self::expr_error(span))
                }
            }
            PPExpr::HasInclude(path, is_angled) => Ok(ExprValue::from_bool(pp.check_header_exists(path, *is_angled))),
            PPExpr::Binary(op, left, right) => Self::eval_binary(*op, left, right, pp, span),
            PPExpr::Unary(op, operand) => Self::eval_unary(*op, operand, pp, span),
            PPExpr::Conditional(cond, true_e, false_e) => Self::eval_conditional(cond, true_e, false_e, pp, span),
        }
    }

    fn expr_error(span: SourceSpan) -> PPError {
        PPError {
            kind: PPErrorKind::InvalidConditionalExpression,
            span,
        }
    }

    fn eval_unary(op: UnaryOp, operand: &PPExpr, pp: &Preprocessor, span: SourceSpan) -> Result<ExprValue, PPError> {
        let o = operand.evaluate(pp, span)?;
        Ok(match op {
            UnaryOp::Plus => o,
            UnaryOp::Minus => ExprValue::new(o.value.wrapping_neg(), o.is_unsigned),
            UnaryOp::BitNot => ExprValue::new(!o.value, o.is_unsigned),
            UnaryOp::LogicNot => ExprValue::from_bool(!o.is_truthy()),
            _ => unreachable!("Unsupported unary operator in preprocessor"),
        })
    }

    fn eval_conditional(
        cond: &PPExpr,
        true_e: &PPExpr,
        false_e: &PPExpr,
        pp: &Preprocessor,
        span: SourceSpan,
    ) -> Result<ExprValue, PPError> {
        let c = cond.evaluate(pp, span)?;
        let t = true_e.evaluate(pp, span)?;
        let f = false_e.evaluate(pp, span)?;
        let is_unsigned = t.is_unsigned || f.is_unsigned;
        let chosen = if c.is_truthy() { t } else { f };
        Ok(if is_unsigned {
            ExprValue::new(chosen.value, true)
        } else {
            chosen
        })
    }

    fn eval_binary(
        op: BinaryOp,
        left: &PPExpr,
        right: &PPExpr,
        pp: &Preprocessor,
        span: SourceSpan,
    ) -> Result<ExprValue, PPError> {
        let l = left.evaluate(pp, span)?;

        // Short-circuit evaluation for logical operators
        if op == BinaryOp::LogicAnd {
            return Ok(ExprValue::from_bool(
                l.is_truthy() && right.evaluate(pp, span)?.is_truthy(),
            ));
        }
        if op == BinaryOp::LogicOr {
            return Ok(ExprValue::from_bool(
                l.is_truthy() || right.evaluate(pp, span)?.is_truthy(),
            ));
        }

        let r = right.evaluate(pp, span)?;
        let is_unsigned = l.is_unsigned || r.is_unsigned;
        let (lv, rv) = (l.value, r.value);

        Ok(match op {
            BinaryOp::BitOr => ExprValue::new(lv | rv, is_unsigned),
            BinaryOp::BitXor => ExprValue::new(lv ^ rv, is_unsigned),
            BinaryOp::BitAnd => ExprValue::new(lv & rv, is_unsigned),
            BinaryOp::Equal => ExprValue::from_bool(lv == rv),
            BinaryOp::NotEqual => ExprValue::from_bool(lv != rv),
            BinaryOp::Less => Self::cmp(lv, rv, is_unsigned, i64::lt, u64::lt),
            BinaryOp::LessEqual => Self::cmp(lv, rv, is_unsigned, i64::le, u64::le),
            BinaryOp::Greater => Self::cmp(lv, rv, is_unsigned, i64::gt, u64::gt),
            BinaryOp::GreaterEqual => Self::cmp(lv, rv, is_unsigned, i64::ge, u64::ge),
            BinaryOp::LShift => ExprValue::new(lv.wrapping_shl(rv as u32), l.is_unsigned),
            BinaryOp::RShift => {
                let shift = rv as u32;
                if l.is_unsigned {
                    ExprValue::new(lv.wrapping_shr(shift), true)
                } else {
                    ExprValue::new(((lv as i64).wrapping_shr(shift)) as u64, false)
                }
            }
            BinaryOp::Add => ExprValue::new(lv.wrapping_add(rv), is_unsigned),
            BinaryOp::Sub => ExprValue::new(lv.wrapping_sub(rv), is_unsigned),
            BinaryOp::Mul => ExprValue::new(lv.wrapping_mul(rv), is_unsigned),
            BinaryOp::Div => Self::eval_div(lv, rv, is_unsigned, span)?,
            BinaryOp::Mod => Self::eval_mod(lv, rv, is_unsigned, span)?,
            _ => unreachable!(),
        })
    }

    fn cmp(
        lv: u64,
        rv: u64,
        is_unsigned: bool,
        signed_f: fn(&i64, &i64) -> bool,
        unsigned_f: fn(&u64, &u64) -> bool,
    ) -> ExprValue {
        ExprValue::from_bool(if is_unsigned {
            unsigned_f(&lv, &rv)
        } else {
            signed_f(&(lv as i64), &(rv as i64))
        })
    }

    fn eval_div(lv: u64, rv: u64, is_unsigned: bool, span: SourceSpan) -> Result<ExprValue, PPError> {
        if rv == 0 {
            return Err(Self::expr_error(span));
        }
        Ok(if is_unsigned {
            ExprValue::new(lv / rv, true)
        } else {
            let (ls, rs) = (lv as i64, rv as i64);
            ExprValue::new(
                if ls == i64::MIN && rs == -1 {
                    ls as u64
                } else {
                    (ls / rs) as u64
                },
                false,
            )
        })
    }

    fn eval_mod(lv: u64, rv: u64, is_unsigned: bool, span: SourceSpan) -> Result<ExprValue, PPError> {
        if rv == 0 {
            return Err(Self::expr_error(span));
        }
        Ok(if is_unsigned {
            ExprValue::new(lv % rv, true)
        } else {
            let (ls, rs) = (lv as i64, rv as i64);
            ExprValue::new(
                if ls == i64::MIN && rs == -1 {
                    0
                } else {
                    (ls % rs) as u64
                },
                false,
            )
        })
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

    fn current_span(&self) -> SourceSpan {
        let loc = self
            .tokens
            .get(self.pos)
            .or_else(|| self.tokens.last())
            .map_or(SourceLoc::builtin(), |t| t.location);
        SourceSpan::new(loc, loc)
    }

    fn error(&self) -> PPError {
        PPError {
            kind: PPErrorKind::InvalidConditionalExpression,
            span: self.current_span(),
        }
    }

    fn peek(&self) -> Option<&PPTokenKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn expect(&mut self, kind: PPTokenKind) -> Result<(), PPError> {
        if self.peek() == Some(&kind) {
            self.advance();
            Ok(())
        } else {
            Err(self.error())
        }
    }

    /// Returns the current token or an error if at the end of the stream.
    fn current(&self) -> Result<&'a PPToken, PPError> {
        if self.at_end() {
            Err(self.error())
        } else {
            Ok(&self.tokens[self.pos])
        }
    }

    /// Returns the current token and advances the position, or returns an error if at the end.
    fn next(&mut self) -> Result<&'a PPToken, PPError> {
        let token = self.current()?;
        self.advance();
        Ok(token)
    }

    pub(crate) fn evaluate(&mut self) -> Result<ExprValue, PPError> {
        let expr = self.parse_conditional()?;
        expr.evaluate(self.preprocessor, self.current_span())
    }

    fn parse_conditional(&mut self) -> Result<PPExpr, PPError> {
        let cond = self.parse_or()?;
        if self.peek() == Some(&PPTokenKind::Question) {
            self.advance();
            let true_e = self.parse_conditional()?;
            self.expect(PPTokenKind::Colon)?;
            let false_e = self.parse_conditional()?;
            Ok(PPExpr::Conditional(Box::new(cond), Box::new(true_e), Box::new(false_e)))
        } else {
            Ok(cond)
        }
    }

    fn parse_or(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(Self::parse_and, &[(PPTokenKind::LogicOr, BinaryOp::LogicOr)])
    }

    fn parse_and(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(Self::parse_bitwise_or, &[(PPTokenKind::LogicAnd, BinaryOp::LogicAnd)])
    }

    fn parse_bitwise_or(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(Self::parse_bitwise_xor, &[(PPTokenKind::Or, BinaryOp::BitOr)])
    }

    fn parse_bitwise_xor(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(Self::parse_bitwise_and, &[(PPTokenKind::Xor, BinaryOp::BitXor)])
    }

    fn parse_bitwise_and(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(Self::parse_equality, &[(PPTokenKind::And, BinaryOp::BitAnd)])
    }

    fn parse_equality(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(
            Self::parse_relational,
            &[
                (PPTokenKind::Equal, BinaryOp::Equal),
                (PPTokenKind::NotEqual, BinaryOp::NotEqual),
            ],
        )
    }

    fn parse_relational(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(
            Self::parse_shift,
            &[
                (PPTokenKind::Less, BinaryOp::Less),
                (PPTokenKind::LessEqual, BinaryOp::LessEqual),
                (PPTokenKind::Greater, BinaryOp::Greater),
                (PPTokenKind::GreaterEqual, BinaryOp::GreaterEqual),
            ],
        )
    }

    fn parse_shift(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(
            Self::parse_additive,
            &[
                (PPTokenKind::LeftShift, BinaryOp::LShift),
                (PPTokenKind::RightShift, BinaryOp::RShift),
            ],
        )
    }

    fn parse_additive(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(
            Self::parse_multiplicative,
            &[(PPTokenKind::Plus, BinaryOp::Add), (PPTokenKind::Minus, BinaryOp::Sub)],
        )
    }

    fn parse_multiplicative(&mut self) -> Result<PPExpr, PPError> {
        self.parse_left_assoc(
            Self::parse_unary,
            &[
                (PPTokenKind::Star, BinaryOp::Mul),
                (PPTokenKind::Slash, BinaryOp::Div),
                (PPTokenKind::Percent, BinaryOp::Mod),
            ],
        )
    }

    /// Generic left-associative binary operator parser.
    fn parse_left_assoc(
        &mut self,
        next: fn(&mut Self) -> Result<PPExpr, PPError>,
        ops: &[(PPTokenKind, BinaryOp)],
    ) -> Result<PPExpr, PPError> {
        let mut left = next(self)?;
        while let Some(kind) = self.peek() {
            if let Some((_, bin_op)) = ops.iter().find(|(tk, _)| tk == kind) {
                self.advance();
                let right = next(self)?;
                left = PPExpr::Binary(*bin_op, Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<PPExpr, PPError> {
        let token = self.current()?;

        // Handle `defined`
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.defined_symbol()) {
            self.advance();
            let ident = if self.peek() == Some(&PPTokenKind::LeftParen) {
                self.advance();
                let ident = self.parse_primary()?;
                self.expect(PPTokenKind::RightParen)?;
                ident
            } else {
                self.parse_primary()?
            };
            return Ok(PPExpr::Defined(Box::new(ident)));
        }

        // Handle `__has_include`
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.has_include_symbol()) {
            self.advance();
            return self.parse_has_include();
        }

        // Handle unary operators
        let unary_op = match token.kind {
            PPTokenKind::Plus => Some(UnaryOp::Plus),
            PPTokenKind::Minus => Some(UnaryOp::Minus),
            PPTokenKind::Tilde => Some(UnaryOp::BitNot),
            PPTokenKind::Not => Some(UnaryOp::LogicNot),
            _ => None,
        };
        if let Some(op) = unary_op {
            self.advance();
            return Ok(PPExpr::Unary(op, Box::new(self.parse_unary()?)));
        }

        self.parse_primary()
    }

    fn parse_has_include(&mut self) -> Result<PPExpr, PPError> {
        self.expect(PPTokenKind::LeftParen)?;
        let token = self.current()?;

        let (path, is_angled) = match &token.kind {
            PPTokenKind::StringLiteral(sym) => {
                let s = sym.as_str();
                if s.starts_with('"') && s.ends_with('"') {
                    self.advance();
                    (s[1..s.len() - 1].to_string(), false)
                } else {
                    return Err(self.error());
                }
            }
            PPTokenKind::Less => {
                self.advance();
                let mut path_str = String::new();
                loop {
                    if self.at_end() {
                        return Err(self.error());
                    }
                    let t = &self.tokens[self.pos];
                    if t.kind == PPTokenKind::Greater {
                        self.advance();
                        break;
                    }
                    path_str.push_str(self.preprocessor.get_token_text(t));
                    self.advance();
                }
                (path_str, true)
            }
            _ => return Err(self.error()),
        };

        self.expect(PPTokenKind::RightParen)?;
        Ok(PPExpr::HasInclude(path, is_angled))
    }

    fn parse_primary(&mut self) -> Result<PPExpr, PPError> {
        let token = self.next()?;

        match &token.kind {
            PPTokenKind::Number(sym) => {
                let text = sym.as_str();
                let (val, suffix) = literal_parsing::parse_c11_integer_literal(text).ok_or_else(|| self.error())?;
                let mut is_unsigned = matches!(suffix, Some(IntegerSuffix::U | IntegerSuffix::UL | IntegerSuffix::ULL));
                if !is_unsigned && val > i64::MAX as u64 {
                    is_unsigned = true;
                }
                Ok(PPExpr::Number(ExprValue::new(val, is_unsigned)))
            }
            PPTokenKind::CharLiteral(codepoint, _) => Ok(PPExpr::Number(ExprValue::new(*codepoint, false))),
            PPTokenKind::Identifier(sym) => Ok(PPExpr::Identifier(sym.as_str().to_string())),
            PPTokenKind::LeftParen => {
                let result = self.parse_conditional()?;
                self.expect(PPTokenKind::RightParen)?;
                Ok(result)
            }
            _ => Err(self.error()),
        }
    }
}
