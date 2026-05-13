use crate::ast::StringId;
use crate::ast::literal::IntSuffix;
use crate::ast::literal_parsing;
use crate::ast::{BinaryOp, UnaryOp};
use crate::pp::{PPError, PPErrorKind, PPKeywordTable, PPToken, PPTokenKind, Preprocessor};
use crate::source_manager::{SourceLoc, SourceSpan};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExprValue {
    pub value: i64,
    pub is_unsigned: bool,
}

impl ExprValue {
    fn new(value: i64, is_unsigned: bool) -> Self {
        ExprValue { value, is_unsigned }
    }

    fn from_bool(b: bool) -> Self {
        ExprValue {
            value: if b { 1 } else { 0 },
            is_unsigned: false,
        }
    }

    pub(super) fn is_truthy(&self) -> bool {
        self.value != 0
    }
}

#[derive(Debug)]
pub(crate) enum PPExpr {
    Number(ExprValue),

    Identifier(StringId),
    Defined(StringId),
    HasInclude(String, bool),
    HasIncludeNext(String, bool),
    HasBuiltin(StringId),
    HasAttribute(StringId),
    HasCAttribute(StringId),
    HasFeature(StringId),
    HasExtension(StringId),
    Binary(BinaryOp, Box<PPExpr>, Box<PPExpr>),
    Unary(UnaryOp, Box<PPExpr>),
    Conditional(Box<PPExpr>, Box<PPExpr>, Box<PPExpr>),
}

impl PPExpr {
    fn evaluate(&self, pp: &Preprocessor, span: SourceSpan) -> Result<ExprValue, PPError> {
        match self {
            PPExpr::Number(n) => Ok(*n),
            PPExpr::Identifier(sym) => {
                if *sym == pp.keywords.c_true {
                    Ok(ExprValue::new(1, false))
                } else {
                    Ok(ExprValue::new(0, false)) // C11 6.10.1p4: All remaining identifiers (including false) are replaced with 0
                }
            }
            PPExpr::Defined(sym) => Ok(ExprValue::from_bool(pp.is_macro_defined(*sym))),
            PPExpr::HasInclude(path, is_angled) => Ok(ExprValue::from_bool(pp.check_header_exists(path, *is_angled))),
            PPExpr::HasIncludeNext(path, is_angled) => {
                Ok(ExprValue::from_bool(pp.check_next_header_exists(path, *is_angled)))
            }
            PPExpr::HasBuiltin(s) => Ok(ExprValue::from_bool(Self::is_builtin_supported(*s, &pp.keywords))),
            PPExpr::HasAttribute(s) => Ok(ExprValue::from_bool(Self::is_attribute_supported(*s, &pp.keywords))),
            PPExpr::HasCAttribute(s) => Ok(ExprValue::new(Self::is_c_attribute_supported(*s, &pp.keywords), false)),
            PPExpr::HasFeature(s) | PPExpr::HasExtension(s) => {
                Ok(ExprValue::from_bool(Self::is_feature_supported(*s, &pp.keywords)))
            }
            PPExpr::Binary(op, left, right) => Self::eval_binary(*op, left, right, pp, span),
            PPExpr::Unary(op, operand) => Self::eval_unary(*op, operand, pp, span),
            PPExpr::Conditional(cond, true_e, false_e) => Self::eval_conditional(cond, true_e, false_e, pp, span),
        }
    }

    fn get_is_unsigned(&self) -> bool {
        match self {
            PPExpr::Number(n) => n.is_unsigned,
            PPExpr::Identifier(_) => false,
            PPExpr::Defined(_) => false,
            PPExpr::HasInclude(_, _) => false,
            PPExpr::HasIncludeNext(_, _) => false,
            PPExpr::HasBuiltin(_) => false,
            PPExpr::HasAttribute(_) => false,
            PPExpr::HasCAttribute(_) => false,
            PPExpr::HasFeature(_) | PPExpr::HasExtension(_) => false,
            PPExpr::Binary(op, left, right) => match op {
                BinaryOp::LogicAnd
                | BinaryOp::LogicOr
                | BinaryOp::Equal
                | BinaryOp::NotEqual
                | BinaryOp::Less
                | BinaryOp::LessEqual
                | BinaryOp::Greater
                | BinaryOp::GreaterEqual => false,
                BinaryOp::LShift | BinaryOp::RShift => left.get_is_unsigned(),
                _ => left.get_is_unsigned() || right.get_is_unsigned(),
            },
            PPExpr::Unary(op, operand) => match op {
                UnaryOp::LogicNot => false,
                _ => operand.get_is_unsigned(),
            },
            PPExpr::Conditional(_, true_e, false_e) => true_e.get_is_unsigned() || false_e.get_is_unsigned(),
        }
    }

    fn is_builtin_supported(name: StringId, kw: &PPKeywordTable) -> bool {
        name == kw.builtin_va_arg
            || name == kw.builtin_va_list
            || name == kw.builtin_va_start
            || name == kw.builtin_va_end
            || name == kw.builtin_va_copy
            || name == kw.builtin_expect
            || name == kw.builtin_memcmp
            || name == kw.builtin_memcpy
            || name == kw.builtin_memset
            || name == kw.builtin_memmove
            || name == kw.builtin_offsetof
            || name == kw.builtin_choose_expr
            || name == kw.builtin_types_compatible_p
            || name == kw.builtin_constant_p
            || name == kw.builtin_unreachable
            || name == kw.builtin_trap
            || name == kw.builtin_prefetch
            || name == kw.builtin_alloca
            || name == kw.builtin_popcount
            || name == kw.builtin_popcountl
            || name == kw.builtin_popcountll
            || name == kw.builtin_clz
            || name == kw.builtin_clzl
            || name == kw.builtin_clzll
            || name == kw.builtin_ctz
            || name == kw.builtin_ctzl
            || name == kw.builtin_ctzll
            || name == kw.builtin_ffs
            || name == kw.builtin_ffsl
            || name == kw.builtin_ffsll
            || name == kw.builtin_bswap16
            || name == kw.builtin_bswap32
            || name == kw.builtin_bswap64
            || name == kw.builtin_fabs
            || name == kw.builtin_fabsf
            || name == kw.builtin_fabsl
            || name == kw.builtin_inf
            || name == kw.builtin_inff
            || name == kw.builtin_huge_val
            || name == kw.builtin_huge_valf
            || name == kw.builtin_nan
            || name == kw.builtin_nanf
            || name == kw.atomic_load_n
            || name == kw.atomic_store_n
            || name == kw.atomic_exchange_n
            || name == kw.atomic_compare_exchange_n
            || name == kw.atomic_fetch_add
            || name == kw.atomic_fetch_sub
            || name == kw.atomic_fetch_and
            || name == kw.atomic_fetch_or
            || name == kw.atomic_fetch_xor
    }

    fn is_attribute_supported(_name: StringId, _kw: &PPKeywordTable) -> bool {
        // We parse and skip all attributes, so technically we "support" them
        // by not failing, but usually __has_attribute returns 1 only for
        // attributes that have semantic meaning for the compiler.
        // For now, return 0 as we don't implement any special attribute semantics.
        false
    }

    fn is_c_attribute_supported(name: StringId, kw: &PPKeywordTable) -> i64 {
        if name == kw.attr_nodiscard
            || name == kw.attr_nodiscard_underscore
            || name == kw.attr_deprecated
            || name == kw.attr_deprecated_underscore
            || name == kw.attr_maybe_unused
            || name == kw.attr_maybe_unused_underscore
            || name == kw.attr_fallthrough
            || name == kw.attr_fallthrough_underscore
        {
            201904
        } else if name == kw.attr_unsequenced
            || name == kw.attr_unsequenced_underscore
            || name == kw.attr_reproducible
            || name == kw.attr_reproducible_underscore
        {
            202311
        } else {
            0
        }
    }

    fn is_feature_supported(name: StringId, kw: &PPKeywordTable) -> bool {
        name == kw.c_static_assert
            || name == kw.c_generic_selection
            || name == kw.c_atomic
            || name == kw.c_alignas
            || name == kw.c_alignof
            || name == kw.c_thread_local
    }

    fn error(kind: PPErrorKind, span: SourceSpan) -> PPError {
        PPError { kind, span }
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
        let chosen = if c.is_truthy() {
            true_e.evaluate(pp, span)?
        } else {
            false_e.evaluate(pp, span)?
        };
        let is_unsigned = true_e.get_is_unsigned() || false_e.get_is_unsigned();
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
                    ExprValue::new((lv as u64).wrapping_shr(shift) as i64, true)
                } else {
                    ExprValue::new(lv.wrapping_shr(shift), false)
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
        lv: i64,
        rv: i64,
        is_unsigned: bool,
        signed_f: fn(&i64, &i64) -> bool,
        unsigned_f: fn(&u64, &u64) -> bool,
    ) -> ExprValue {
        ExprValue::from_bool(if is_unsigned {
            unsigned_f(&(lv as u64), &(rv as u64))
        } else {
            signed_f(&lv, &rv)
        })
    }

    fn eval_div(lv: i64, rv: i64, is_unsigned: bool, span: SourceSpan) -> Result<ExprValue, PPError> {
        if rv == 0 {
            return Err(Self::error(PPErrorKind::DivisionByZero, span));
        }
        Ok(if is_unsigned {
            ExprValue::new(((lv as u64) / (rv as u64)) as i64, true)
        } else {
            ExprValue::new(if lv == i64::MIN && rv == -1 { lv } else { lv / rv }, false)
        })
    }

    fn eval_mod(lv: i64, rv: i64, is_unsigned: bool, span: SourceSpan) -> Result<ExprValue, PPError> {
        if rv == 0 {
            return Err(Self::error(PPErrorKind::RemainderByZero, span));
        }
        Ok(if is_unsigned {
            ExprValue::new(((lv as u64) % (rv as u64)) as i64, true)
        } else {
            ExprValue::new(if lv == i64::MIN && rv == -1 { 0 } else { lv % rv }, false)
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
        SourceSpan::from_loc(loc)
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
            let sym = if self.peek() == Some(&PPTokenKind::LeftParen) {
                self.advance();
                let sym = self.expect_identifier()?;
                self.expect(PPTokenKind::RightParen)?;
                sym
            } else {
                self.expect_identifier()?
            };
            return Ok(PPExpr::Defined(sym));
        }

        // Handle `__has_include`
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.has_include_symbol()) {
            self.advance();
            return self.parse_has_include(false);
        }

        // Handle `__has_include_next`
        if matches!(token.kind, PPTokenKind::Identifier(sym) if sym == self.preprocessor.has_include_next_symbol()) {
            self.advance();
            return self.parse_has_include(true);
        }

        // Handle `__has_builtin` and friends
        let checks = [
            (
                self.preprocessor.has_builtin_symbol(),
                PPExpr::HasBuiltin as fn(StringId) -> PPExpr,
            ),
            (self.preprocessor.has_attribute_symbol(), PPExpr::HasAttribute),
            (self.preprocessor.has_c_attribute_symbol(), PPExpr::HasCAttribute),
            (self.preprocessor.has_feature_symbol(), PPExpr::HasFeature),
            (self.preprocessor.has_extension_symbol(), PPExpr::HasExtension),
        ];

        if let PPTokenKind::Identifier(sym) = token.kind {
            for (id, constructor) in checks {
                if sym == id {
                    self.advance();
                    return self.parse_has_builtin_style(constructor);
                }
            }
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

    fn parse_has_include(&mut self, is_next: bool) -> Result<PPExpr, PPError> {
        self.expect(PPTokenKind::LeftParen)?;
        let token = self.current()?;

        let (path, is_angled) = match &token.kind {
            PPTokenKind::StringLiteral => {
                let s = self.preprocessor.get_token_text(token);
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
                    path_str.push_str(&self.preprocessor.get_token_text(t));
                    self.advance();
                }
                (path_str, true)
            }
            _ => return Err(self.error()),
        };

        self.expect(PPTokenKind::RightParen)?;
        if is_next {
            Ok(PPExpr::HasIncludeNext(path, is_angled))
        } else {
            Ok(PPExpr::HasInclude(path, is_angled))
        }
    }

    fn parse_has_builtin_style(&mut self, f: impl FnOnce(StringId) -> PPExpr) -> Result<PPExpr, PPError> {
        self.expect(PPTokenKind::LeftParen)?;
        let sym = self.expect_identifier()?;
        self.expect(PPTokenKind::RightParen)?;
        Ok(f(sym))
    }

    fn expect_identifier(&mut self) -> Result<StringId, PPError> {
        let token = self.next()?;
        match &token.kind {
            PPTokenKind::Identifier(sym) => Ok(*sym),
            _ => Err(self.error()),
        }
    }

    fn parse_primary(&mut self) -> Result<PPExpr, PPError> {
        let token = self.next()?;

        match &token.kind {
            PPTokenKind::Number => {
                let text = self.preprocessor.get_token_text(token);
                let (val, suffix, _) = literal_parsing::parse_integer_literal(&text).ok_or_else(|| self.error())?;
                let mut is_unsigned = matches!(suffix, Some(IntSuffix::U | IntSuffix::UL | IntSuffix::ULL));
                if !is_unsigned && (val as u64) > i64::MAX as u64 {
                    is_unsigned = true;
                }
                Ok(PPExpr::Number(ExprValue::new(val, is_unsigned)))
            }
            PPTokenKind::CharLiteral(codepoint) => Ok(PPExpr::Number(ExprValue::new(*codepoint as i64, false))),
            PPTokenKind::Identifier(sym) => Ok(PPExpr::Identifier(*sym)),
            PPTokenKind::LeftParen => {
                let result = self.parse_conditional()?;
                self.expect(PPTokenKind::RightParen)?;
                Ok(result)
            }
            _ => Err(self.error()),
        }
    }
}
