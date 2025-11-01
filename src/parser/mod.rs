use crate::common::SourceSpan;
use crate::parser::ast::{
    Designator, Expr, ForInit, Function, Initializer, InitializerList, Parameter, Stmt,
    TranslationUnit, Type,
};
use crate::parser::error::ParserError;
use crate::parser::string_interner::StringId;
use crate::parser::token::{KeywordKind, Token, TokenKind};
use crate::preprocessor;
use std::collections::HashMap;
use thin_vec::ThinVec;

pub mod ast;
pub mod error;
pub mod string_interner;
pub mod token;

pub struct FunctionSignature(Type, StringId, ThinVec<Parameter>, bool, bool, bool);

/// A parser that converts a stream of tokens into an abstract syntax tree.
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    typedefs: HashMap<StringId, Type>,
}

impl Parser {
    /// Creates a new `Parser`.
    ///
    /// # Arguments
    ///
    /// * `tokens` - A vector of preprocessor tokens.
    ///
    /// # Returns
    ///
    /// A `Result` containing the new `Parser` instance, or a `ParserError` if tokenization fails.
    pub fn new(tokens: Vec<preprocessor::token::Token>) -> Result<Self, ParserError> {
        // Filter out tokens that the parser can't handle
        let mut filtered_tokens: Vec<Token> = Vec::new();
        let mut skip_next_tokens = false;

        for token in tokens {
            match &token.kind {
                preprocessor::token::TokenKind::Directive(_) => {
                    skip_next_tokens = true;
                    continue;
                }
                preprocessor::token::TokenKind::Whitespace(_)
                | preprocessor::token::TokenKind::Newline
                | preprocessor::token::TokenKind::Comment(_) => {
                    continue;
                }
                // Skip tokens that come from directive expansions
                _ if !token.expansion_locs.is_empty() => {
                    continue;
                }
                // Skip tokens that immediately follow a directive (like line directive arguments)
                _ if skip_next_tokens => {
                    // Check if this is likely a directive argument (Number or String at the beginning)
                    if (matches!(
                        token.kind,
                        preprocessor::token::TokenKind::Number(_)
                            | preprocessor::token::TokenKind::String(_)
                    )) && filtered_tokens.is_empty()
                    {
                        continue;
                    }
                    skip_next_tokens = false;
                }
                _ => {}
            }
            filtered_tokens.push(Token::from(token));
        }

        let parser = Parser {
            tokens: filtered_tokens,
            position: 0,
            typedefs: HashMap::new(),
        };
        Ok(parser)
    }

    /// Returns the current token without consuming it.
    fn current_token(&self) -> Result<Token, ParserError> {
        self.tokens
            .get(self.position)
            .cloned()
            .ok_or(ParserError::UnexpectedEof)
    }

    /// Returns the kind of the current token.
    fn current_kind(&self) -> Result<TokenKind, ParserError> {
        self.current_token().map(|t| t.kind)
    }

    fn peek(&self) -> Result<TokenKind, ParserError> {
        self.tokens
            .get(self.position + 1)
            .cloned()
            .map(|t| t.kind)
            .ok_or(ParserError::UnexpectedEof)
    }

    /// Consumes the current token and return the last token. will error if current token is eof
    fn eat(&mut self) -> Result<&Token, ParserError> {
        let current = self
            .tokens
            .get(self.position)
            .ok_or(ParserError::UnexpectedEof);
        self.position += 1;
        current
    }

    /// consume the current token if same kind
    fn eat_token(&mut self, kind: &TokenKind) -> Result<bool, ParserError> {
        if self.current_kind()? == *kind {
            self.eat()?;
            return Ok(true);
        }
        Ok(false)
    }

    /// Expects a specific punctuation token.
    fn expect_punct(&mut self, value: TokenKind) -> Result<(), ParserError> {
        if self.eat_token(&value)? {
            return Ok(());
        }
        let token = self.current_token()?;
        Err(ParserError::UnexpectedToken(token))
    }

    /// Expects a specific keyword.
    fn expect_keyword(&mut self, value: KeywordKind) -> Result<(), ParserError> {
        if self.eat_token(&TokenKind::Keyword(value))? {
            return Ok(());
        }
        let token = self.current_token()?;
        Err(ParserError::UnexpectedToken(token))
    }

    /// Peeks if the current token sequence is a type name without consuming tokens.
    fn is_type_name(&mut self) -> bool {
        let original_pos = self.position;
        let result = self.parse_type().is_ok();
        self.position = original_pos;
        result
    }

    /// Expects and consumes an optional identifier, returning its name if present.
    fn maybe_name(&mut self) -> Result<Option<StringId>, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind {
            self.eat()?;
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    /// Expects and consumes an identifier, returning its name.
    fn expect_name(&mut self) -> Result<StringId, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind {
            self.eat()?;
            Ok(id)
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses a type specifier (e.g., `int`, `struct S`, `long long`).
    fn parse_type_specifier(&mut self) -> Result<Type, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == KeywordKind::Const {
                self.eat()?;
                let ty = self.parse_type_specifier()?;
                return Ok(Type::Const(Box::new(ty)));
            }
            if k == KeywordKind::Volatile {
                self.eat()?;
                let ty = self.parse_type_specifier()?;
                return Ok(Type::Volatile(Box::new(ty)));
            }
            self.parse_type_specifier_kind(k)
        } else if let TokenKind::Identifier(id) = token.kind.clone() {
            if let Some(ty) = self.typedefs.get(&id).cloned() {
                self.eat()?;
                Ok(ty)
            } else {
                Err(ParserError::UnexpectedToken(token))
            }
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses a type specifier kind.
    fn parse_type_specifier_kind(&mut self, k: KeywordKind) -> Result<Type, ParserError> {
        let token = self.current_token()?;
        match k {
            KeywordKind::Unsigned => {
                self.eat()?; // consume "unsigned"
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token {
                    if let TokenKind::Keyword(KeywordKind::Long) = next.kind {
                        self.eat()?; // consume "long"
                        let next2 = self.tokens.get(self.position).cloned();
                        if let Some(n2) = next2 {
                            if let TokenKind::Keyword(KeywordKind::Long) = n2.kind {
                                self.eat()?; // consume second "long"
                                Ok(Type::UnsignedLongLong)
                            } else {
                                Ok(Type::UnsignedLong)
                            }
                        } else {
                            Ok(Type::UnsignedLong)
                        }
                    } else if let TokenKind::Keyword(KeywordKind::Int) = next.kind {
                        self.eat()?; // consume "int"
                        Ok(Type::UnsignedInt)
                    } else if let TokenKind::Keyword(KeywordKind::Char) = next.kind {
                        self.eat()?; // consume "char"
                        Ok(Type::UnsignedChar)
                    } else if let TokenKind::Keyword(KeywordKind::Short) = next.kind {
                        self.eat()?; // consume "short"
                        Ok(Type::UnsignedShort)
                    } else {
                        Ok(Type::UnsignedInt)
                    }
                } else {
                    Ok(Type::UnsignedInt)
                }
            }
            KeywordKind::Short => {
                self.eat()?; // consume "short"
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token
                    && let TokenKind::Keyword(KeywordKind::Int) = next.kind
                {
                    self.eat()?; // consume "int"
                }
                Ok(Type::Short)
            }
            KeywordKind::Long => {
                self.eat()?; // consume "long"
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token {
                    if let TokenKind::Keyword(KeywordKind::Long) = next.kind {
                        self.eat()?; // consume second "long"
                        let next2 = self.tokens.get(self.position).cloned();
                        if let Some(n2) = next2
                            && let TokenKind::Keyword(KeywordKind::Int) = n2.kind
                        {
                            self.eat()?; // consume "int"
                        }
                        Ok(Type::LongLong)
                    } else if let TokenKind::Keyword(KeywordKind::Int) = next.kind {
                        self.eat()?; // consume "int"
                        Ok(Type::Long)
                    } else {
                        Ok(Type::Long)
                    }
                } else {
                    Ok(Type::Long)
                }
            }
            KeywordKind::Int => self.parse_simple_type(Type::Int),
            KeywordKind::Char => self.parse_simple_type(Type::Char),
            KeywordKind::Float => self.parse_simple_type(Type::Float),
            KeywordKind::Double => self.parse_simple_type(Type::Double),
            KeywordKind::Void => self.parse_simple_type(Type::Void),
            KeywordKind::Bool => self.parse_simple_type(Type::Bool),
            KeywordKind::Struct => self.parse_struct_or_union(|name, members| {
                if let Some(members) = members {
                    Type::Struct(name, members)
                } else if let Some(name) = name {
                    Type::Struct(Some(name), ThinVec::new())
                } else {
                    unreachable!()
                }
            }),
            KeywordKind::Union => self.parse_struct_or_union(|name, members| {
                if let Some(members) = members {
                    Type::Union(name, members)
                } else if let Some(name) = name {
                    Type::Union(Some(name), ThinVec::new())
                } else {
                    unreachable!()
                }
            }),
            KeywordKind::Enum => self.parse_enum_specifier(),
            _ => Err(ParserError::UnexpectedToken(token)),
        }
    }
    /// Parses a simple type keyword and returns the corresponding `Type`.
    fn parse_simple_type(&mut self, ty: Type) -> Result<Type, ParserError> {
        self.eat()?;
        Ok(ty)
    }

    /// Parses an enum specifier.
    fn parse_enum_specifier(&mut self) -> Result<Type, ParserError> {
        self.eat()?; // consume 'enum'
        let name = self.maybe_name()?;
        if self.eat_token(&TokenKind::LeftBrace)? {
            let mut enumerators = ThinVec::new();
            if !self.eat_token(&TokenKind::RightBrace)? {
                loop {
                    enumerators.push(self.parse_enumerator()?);
                    if !self.eat_token(&TokenKind::Comma)? {
                        self.expect_punct(TokenKind::RightBrace)?;
                        break;
                    }
                    if self.eat_token(&TokenKind::RightBrace)? {
                        break;
                    }
                }
            }
            Ok(Type::Enum(name, enumerators))
        } else if let Some(name) = name {
            Ok(Type::Enum(Some(name), ThinVec::new()))
        } else {
            let token = self.current_token()?;
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses a single enumerator.
    fn parse_enumerator(
        &mut self,
    ) -> Result<(StringId, Option<Box<Expr>>, SourceSpan), ParserError> {
        let token = self.current_token()?;
        let name = self.expect_name()?;
        if self.eat_token(&TokenKind::Equal)? {
            let expr = self.parse_pratt_expr(2)?; // Assignment precedence
            Ok((name, Some(Box::new(expr)), token.span))
        } else {
            Ok((name, None, token.span))
        }
    }

    /// Parses a struct or union type.
    fn parse_struct_or_union<F>(&mut self, constructor: F) -> Result<Type, ParserError>
    where
        F: Fn(Option<StringId>, Option<ThinVec<Parameter>>) -> Type,
    {
        self.eat()?;
        let name = self.maybe_name()?;
        match self.current_kind()? {
            TokenKind::LeftBrace => {
                let members = self.parse_struct_or_union_members()?;
                Ok(constructor(name, Some(members)))
            }
            _ if name.is_some() => Ok(constructor(name, None)),
            _ => {
                let token = self.current_token()?;
                Err(ParserError::UnexpectedToken(token))
            }
        }
    }
    /// Parses members for struct or union.
    fn parse_struct_or_union_members(&mut self) -> Result<ThinVec<Parameter>, ParserError> {
        self.parse_delimited_list(
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::Semicolon,
            |p| {
                let base_ty = p.parse_type_specifier()?;
                let (ty, name, id_token) = p.parse_declarator_suffix(base_ty, true)?;
                Ok(Parameter {
                    ty,
                    name,
                    span: id_token.span,
                })
            },
        )
    }

    /// Parses declarator suffixes (pointers and arrays) and returns the final type and identifier.
    /// This function assumes the base type has already been parsed.
    fn parse_declarator_suffix(
        &mut self,
        base_type: Type,
        name_required: bool,
    ) -> Result<(Type, StringId, Token), ParserError> {
        let mut ty = base_type;

        // Parse pointers
        while self.eat_token(&TokenKind::Star)? {
            ty = Type::Pointer(Box::new(ty));
            while self.eat_token(&TokenKind::Keyword(KeywordKind::Const))? {
                ty = Type::Const(Box::new(ty));
            }
            while self.eat_token(&TokenKind::Keyword(KeywordKind::Volatile))? {
                ty = Type::Volatile(Box::new(ty));
            }
        }

        let id_token = self.current_token()?;
        let (id, final_token) = if let TokenKind::Identifier(name) = id_token.kind.clone() {
            self.eat()?;
            (name, id_token)
        } else {
            if name_required {
                return Err(ParserError::UnexpectedToken(id_token));
            }
            // For abstract declarators, there's no identifier.
            // We'll pass back the token we're at, but the caller must be careful.
            // Let's create a default token to signify no identifier.
            (
                crate::parser::string_interner::StringInterner::empty_id(), // Use empty string for default StringId
                Token {
                    span: Default::default(),
                    kind: TokenKind::Eof,
                },
            )
        };

        // Parse array dimensions
        while self.eat_token(&TokenKind::LeftBracket)? {
            if self.eat_token(&TokenKind::RightBracket)? {
                ty = Type::Array(Box::new(ty), 0); // Unsized array
            } else {
                let size_expr = self.parse_expr()?;
                let size = if let Expr::Number(n, _) = size_expr {
                    n as usize
                } else {
                    let token = self.current_token()?;
                    return Err(ParserError::UnexpectedToken(token));
                };
                self.expect_punct(TokenKind::RightBracket)?;
                ty = Type::Array(Box::new(ty), size);
            }
        }
        Ok((ty, id, final_token))
    }

    /// Parses a declarator with optional initializer.
    fn parse_declarator(
        &mut self,
        base_type: Type,
        name_required: bool,
    ) -> Result<ast::Declarator, ParserError> {
        let (ty, name, id_token) = self.parse_declarator_suffix(base_type, name_required)?;
        let initializer = self.parse_initializer_expr()?;
        Ok(ast::Declarator {
            ty,
            name,
            initializer,
            span: id_token.span,
        })
    }

    /// parse initializer expression
    fn parse_initializer_expr(&mut self) -> Result<Option<Initializer>, ParserError> {
        self.maybe_start(&TokenKind::Equal, |p| p.parse_initializer())
    }

    /// Parses a C initializer.
    fn parse_initializer(&mut self) -> Result<Initializer, ParserError> {
        if self.eat_token(&TokenKind::LeftBrace)? {
            let list = self.parse_initializer_list()?;
            self.expect_punct(TokenKind::RightBrace)?;
            Ok(Initializer::List(list))
        } else {
            let expr = self.parse_pratt_expr(2)?; // Assignment precedence
            Ok(Initializer::Expr(Box::new(expr)))
        }
    }

    /// Parses a type. This function now orchestrates `parse_type_specifier` and `parse_declarator_suffix`.
    fn parse_type(&mut self) -> Result<Type, ParserError> {
        let base_type = self.parse_type_specifier()?;
        // For abstract declarators (e.g., `int *`), there might not be an identifier immediately.
        // This function is primarily for parsing a full type with a declarator.
        // If we are just parsing a type for a cast or sizeof, we might not have an identifier.
        // The `is_type_name` function will handle backtracking if no identifier is found.
        let original_pos = self.position;
        if let Ok(kind) = self.current_kind()
            && matches!(kind, TokenKind::Star | TokenKind::LeftBracket)
            && let Ok((ty, _, _)) = self.parse_declarator_suffix(base_type.clone(), false)
        {
            return Ok(ty);
        }
        self.position = original_pos; // Backtrack if no declarator suffix found
        Ok(base_type)
    }

    /// Parses an expression.
    fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        self.parse_pratt_expr(0)
    }

    /// Gets the prefix binding power of a token.
    fn prefix_binding_power(&self, kind: &TokenKind) -> Option<((), u8)> {
        match kind {
            TokenKind::Plus | TokenKind::Minus | TokenKind::PlusPlus | TokenKind::MinusMinus => {
                Some(((), 15))
            }
            TokenKind::Bang | TokenKind::Tilde => Some(((), 15)),
            TokenKind::Keyword(KeywordKind::Sizeof) => Some(((), 15)),
            TokenKind::Keyword(KeywordKind::Alignof) => Some(((), 15)),
            _ => None,
        }
    }

    /// Gets the postfix binding power of a token.
    fn postfix_binding_power(&self, kind: &TokenKind) -> Option<(u8, ())> {
        match kind {
            TokenKind::PlusPlus | TokenKind::MinusMinus => Some((17, ())),
            _ => None,
        }
    }

    /// Gets the infix binding power of a token.
    fn infix_binding_power(&self, kind: &TokenKind) -> Option<(u8, u8)> {
        match kind {
            TokenKind::Comma => Some((2, 1)),
            TokenKind::PipePipe => Some((3, 4)),
            TokenKind::AmpersandAmpersand => Some((5, 6)),
            TokenKind::Pipe => Some((7, 8)),
            TokenKind::Caret => Some((9, 10)),
            TokenKind::Ampersand => Some((11, 12)),
            TokenKind::EqualEqual | TokenKind::BangEqual => Some((13, 14)),
            TokenKind::LessThan
            | TokenKind::GreaterThan
            | TokenKind::LessThanEqual
            | TokenKind::GreaterThanEqual => Some((15, 16)),
            TokenKind::LessThanLessThan | TokenKind::GreaterThanGreaterThan => Some((17, 18)),
            TokenKind::Plus | TokenKind::Minus => Some((19, 20)),
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Some((21, 22)),
            TokenKind::Arrow | TokenKind::Dot => Some((23, 24)),
            TokenKind::Equal
            | TokenKind::PlusEqual
            | TokenKind::MinusEqual
            | TokenKind::AsteriskEqual
            | TokenKind::SlashEqual
            | TokenKind::PercentEqual
            | TokenKind::LessThanLessThanEqual
            | TokenKind::GreaterThanGreaterThanEqual
            | TokenKind::AmpersandEqual
            | TokenKind::CaretEqual
            | TokenKind::PipeEqual => Some((4, 3)),
            _ => None,
        }
    }
    /// Creates a binary expression based on the operator token.
    fn create_binary_expr(&self, lhs: Expr, rhs: Expr, op: TokenKind) -> Result<Expr, ParserError> {
        if op.is_assignment() {
            let lhs = Box::new(lhs);
            let rhs = Box::new(rhs);
            match op {
                TokenKind::Equal => Ok(Expr::Assign(lhs, rhs)),
                TokenKind::PlusEqual => Ok(Expr::AssignAdd(lhs, rhs)),
                TokenKind::MinusEqual => Ok(Expr::AssignSub(lhs, rhs)),
                TokenKind::AsteriskEqual => Ok(Expr::AssignMul(lhs, rhs)),
                TokenKind::SlashEqual => Ok(Expr::AssignDiv(lhs, rhs)),
                TokenKind::PercentEqual => Ok(Expr::AssignMod(lhs, rhs)),
                TokenKind::LessThanLessThanEqual => Ok(Expr::AssignLeftShift(lhs, rhs)),
                TokenKind::GreaterThanGreaterThanEqual => Ok(Expr::AssignRightShift(lhs, rhs)),
                TokenKind::AmpersandEqual => Ok(Expr::AssignBitwiseAnd(lhs, rhs)),
                TokenKind::CaretEqual => Ok(Expr::AssignBitwiseXor(lhs, rhs)),
                TokenKind::PipeEqual => Ok(Expr::AssignBitwiseOr(lhs, rhs)),
                _ => unreachable!(),
            }
        } else {
            let lhs = Box::new(lhs);
            let rhs = Box::new(rhs);
            match op {
                TokenKind::Comma => Ok(Expr::Comma(lhs, rhs)),
                TokenKind::Plus => Ok(Expr::Add(lhs, rhs)),
                TokenKind::Minus => Ok(Expr::Sub(lhs, rhs)),
                TokenKind::Star => Ok(Expr::Mul(lhs, rhs)),
                TokenKind::Slash => Ok(Expr::Div(lhs, rhs)),
                TokenKind::Percent => Ok(Expr::Mod(lhs, rhs)),
                TokenKind::EqualEqual => Ok(Expr::Equal(lhs, rhs)),
                TokenKind::BangEqual => Ok(Expr::NotEqual(lhs, rhs)),
                TokenKind::LessThan => Ok(Expr::LessThan(lhs, rhs)),
                TokenKind::GreaterThan => Ok(Expr::GreaterThan(lhs, rhs)),
                TokenKind::LessThanEqual => Ok(Expr::LessThanOrEqual(lhs, rhs)),
                TokenKind::GreaterThanEqual => Ok(Expr::GreaterThanOrEqual(lhs, rhs)),
                TokenKind::AmpersandAmpersand => Ok(Expr::LogicalAnd(lhs, rhs)),
                TokenKind::PipePipe => Ok(Expr::LogicalOr(lhs, rhs)),
                TokenKind::Pipe => Ok(Expr::BitwiseOr(lhs, rhs)),
                TokenKind::Caret => Ok(Expr::BitwiseXor(lhs, rhs)),
                TokenKind::Ampersand => Ok(Expr::BitwiseAnd(lhs, rhs)),
                TokenKind::LessThanLessThan => Ok(Expr::LeftShift(lhs, rhs)),
                TokenKind::GreaterThanGreaterThan => Ok(Expr::RightShift(lhs, rhs)),
                _ => unreachable!(),
            }
        }
    }

    /// Parses an expression using the Pratt parsing algorithm.
    fn parse_pratt_expr(&mut self, min_bp: u8) -> Result<Expr, ParserError> {
        let mut lhs = if let Some(((), r_bp)) = self.prefix_binding_power(&self.current_kind()?) {
            let kind = self.current_kind()?;
            self.eat()?;
            match kind {
                TokenKind::PlusPlus => {
                    let expr = self.parse_pratt_expr(r_bp)?;
                    Expr::PreIncrement(Box::new(expr))
                }
                TokenKind::MinusMinus => {
                    let expr = self.parse_pratt_expr(r_bp)?;
                    Expr::PreDecrement(Box::new(expr))
                }
                TokenKind::Plus => self.parse_pratt_expr(r_bp)?,
                TokenKind::Minus => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::Neg(Box::new(rhs))
                }
                TokenKind::Bang => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::LogicalNot(Box::new(rhs))
                }
                TokenKind::Tilde => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::BitwiseNot(Box::new(rhs))
                }
                TokenKind::Keyword(KeywordKind::Sizeof) => {
                    if self.eat_token(&TokenKind::LeftParen)? {
                        let expr = if self.is_type_name() {
                            let ty = self.parse_type()?;
                            Expr::SizeofType(ty)
                        } else {
                            let expr = self.parse_expr()?;
                            Expr::Sizeof(Box::new(expr))
                        };
                        self.expect_punct(TokenKind::RightParen)?;
                        expr
                    } else {
                        let expr = self.parse_pratt_expr(r_bp)?;
                        Expr::Sizeof(Box::new(expr))
                    }
                }
                TokenKind::Keyword(KeywordKind::Alignof) => {
                    if self.eat_token(&TokenKind::LeftParen)? {
                        let expr = if self.is_type_name() {
                            let ty = self.parse_type()?;
                            Expr::AlignofType(ty)
                        } else {
                            let expr = self.parse_expr()?;
                            Expr::Alignof(Box::new(expr))
                        };
                        self.expect_punct(TokenKind::RightParen)?;
                        expr
                    } else {
                        let expr = self.parse_pratt_expr(r_bp)?;
                        Expr::Alignof(Box::new(expr))
                    }
                }
                _ => unreachable!(),
            }
        } else {
            self.parse_primary()?
        };

        loop {
            let kind = self.current_kind()?;
            if let Some((l_bp, ())) = self.postfix_binding_power(&kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;

                lhs = match kind {
                    TokenKind::PlusPlus => Expr::PostIncrement(Box::new(lhs)),
                    TokenKind::MinusMinus => Expr::PostDecrement(Box::new(lhs)),
                    _ => unreachable!(),
                };
                continue;
            }
            if let Some((l_bp, r_bp)) = self.infix_binding_power(&kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;
                let rhs = self.parse_pratt_expr(r_bp)?;

                lhs = match kind {
                    TokenKind::Arrow => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::PointerMember(Box::new(lhs), name)
                        } else {
                            let token = self.current_token()?;
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    TokenKind::Dot => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::Member(Box::new(lhs), name)
                        } else {
                            let token = self.current_token()?;
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    _ => self.create_binary_expr(lhs, rhs, kind)?,
                };
                continue;
            }
            if kind == TokenKind::Question {
                let (l_bp, r_bp) = (5, 4);
                if l_bp < min_bp {
                    break;
                }
                self.eat()?; // Consume '?'
                let then_expr = self.parse_pratt_expr(0)?;
                self.expect_punct(TokenKind::Colon)?;
                let else_expr = self.parse_pratt_expr(r_bp)?;
                lhs = Expr::Ternary(Box::new(lhs), Box::new(then_expr), Box::new(else_expr));
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    /// Parses a primary expression.
    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.eat()?;
                let num_str = n.as_str();
                if num_str.contains('.') || num_str.contains('e') || num_str.contains('E') {
                    let trimmed = num_str.trim_end_matches(['f', 'F', 'l', 'L']);
                    Ok(Expr::FloatNumber(trimmed.parse().unwrap(), token.span))
                } else {
                    let trimmed = num_str.trim_end_matches(['L', 'U', 'l', 'u']);
                    Ok(Expr::Number(trimmed.parse().unwrap(), token.span))
                }
            }
            TokenKind::String(s) => {
                self.eat()?;
                Ok(Expr::String(s, token.span))
            }
            TokenKind::Char(s) => {
                self.eat()?;
                Ok(Expr::Char(s, token.span))
            }
            TokenKind::Identifier(name) => {
                self.eat()?;
                let mut expr = Expr::Variable(name, token.span);
                while let Ok(token) = self.current_token() {
                    match token.kind {
                        TokenKind::LeftParen => {
                            let location = if let Expr::Variable(_, span) = expr {
                                span
                            } else {
                                token.span
                            };
                            let token_for_error = token.clone();
                            self.eat()?; // consume '('
                            let mut args = ThinVec::new();
                            if self.current_token()?.kind != TokenKind::RightParen {
                                loop {
                                    // Use a binding power of 2 to stop parsing at a comma
                                    args.push(self.parse_pratt_expr(2)?);
                                    if self.current_token()?.kind == TokenKind::RightParen {
                                        break;
                                    }
                                    self.expect_punct(TokenKind::Comma)?;
                                }
                            }
                            self.expect_punct(TokenKind::RightParen)?;
                            let name = match expr {
                                Expr::Variable(name, _) => name,
                                _ => return Err(ParserError::UnexpectedToken(token_for_error)),
                            };
                            expr = Expr::Call(name, args, location);
                        }
                        TokenKind::LeftBracket => {
                            self.eat()?;
                            let index = self.parse_expr()?;
                            self.expect_punct(TokenKind::RightBracket)?;
                            let add = Expr::Add(Box::new(expr), Box::new(index));
                            expr = Expr::Deref(Box::new(add));
                        }
                        _ => break,
                    }
                }
                Ok(expr)
            }
            TokenKind::Star => {
                self.eat()?;
                let expr = self.parse_primary()?;
                Ok(Expr::Deref(Box::new(expr)))
            }
            TokenKind::Ampersand => {
                self.eat()?;
                let expr = self.parse_pratt_expr(15)?;
                Ok(Expr::AddressOf(Box::new(expr)))
            }
            TokenKind::Minus => {
                self.eat()?;
                let expr = self.parse_pratt_expr(7)?;
                Ok(Expr::Neg(Box::new(expr)))
            }
            TokenKind::Plus => {
                self.eat()?;
                self.parse_pratt_expr(7)
            }
            TokenKind::Bang => {
                self.eat()?;
                let expr = self.parse_pratt_expr(15)?;
                Ok(Expr::LogicalNot(Box::new(expr)))
            }
            TokenKind::LeftParen => {
                self.eat()?; // Consume '('

                // Check for cast or compound literal
                let pos = self.position;
                let is_type = if let Ok(_ty) = self.parse_type() {
                    if let Ok(token) = self.current_token() {
                        token.kind == TokenKind::RightParen
                    } else {
                        false
                    }
                } else {
                    false
                };
                self.position = pos; // backtrack after peeking

                if is_type {
                    let param_ty = self.parse_type()?;
                    self.expect_punct(TokenKind::RightParen)?;

                    if let Ok(TokenKind::LeftBrace) = self.current_kind() {
                        // Compound Literal: (type){...}
                        let initializer = self.parse_initializer()?;
                        Ok(Expr::CompoundLiteral(
                            Box::new(param_ty),
                            Box::new(initializer),
                        ))
                    } else {
                        // Cast: (type)expr
                        let expr = self.parse_pratt_expr(15)?; // High precedence for cast's operand
                        Ok(Expr::ExplicitCast(Box::new(param_ty), Box::new(expr)))
                    }
                } else {
                    // Grouped expression: (expr)
                    let expr = self.parse_expr()?;
                    self.expect_punct(TokenKind::RightParen)?;
                    Ok(expr)
                }
            }
            TokenKind::LeftBrace => {
                let initializers = self.parse_initializer_list()?;
                self.expect_punct(TokenKind::RightBrace)?;
                Ok(Expr::InitializerList(initializers))
            }
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }

    fn parse_designator(&mut self) -> Result<ThinVec<Designator>, ParserError> {
        let mut designators = ThinVec::new();
        loop {
            if self.eat_token(&TokenKind::Dot)? {
                let member = self.expect_name()?;
                designators.push(Designator::Member(member));
            } else if self.eat_token(&TokenKind::LeftBracket)? {
                let index = self.parse_expr()?;
                self.expect_punct(TokenKind::RightBracket)?;
                designators.push(Designator::Index(Box::new(index)));
            } else {
                break;
            }
        }
        Ok(designators)
    }

    /// Parses an initializer list.
    fn parse_initializer_list(&mut self) -> Result<InitializerList, ParserError> {
        let mut initializers = ThinVec::new();
        if self.eat_token(&TokenKind::RightBrace)? {
            return Ok(initializers);
        }

        loop {
            let designators = self.parse_designator()?;
            let initializer = if !designators.is_empty() {
                self.expect_punct(TokenKind::Equal)?;
                self.parse_initializer()?
            } else {
                // Use a binding power of 2 to stop parsing at a comma
                Initializer::Expr(Box::new(self.parse_pratt_expr(2)?))
            };
            initializers.push((designators, Box::new(initializer)));

            if !self.eat_token(&TokenKind::Comma)? {
                break;
            }

            if self.eat_token(&TokenKind::RightBrace)? {
                break;
            }
        }
        Ok(initializers)
    }

    /// Parses a statement.
    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        if self.current_kind()? == TokenKind::Keyword(KeywordKind::StaticAssert) {
            return self.parse_static_assert();
        }
        let token = self.current_token()?;
        if let TokenKind::LeftBrace = token.kind.clone() {
            self.eat()?;
            let mut stmts = ThinVec::new();
            while self.eat_token(&TokenKind::RightBrace)? == false {
                stmts.push(self.parse_stmt()?);
            }
            return Ok(Stmt::Block(stmts));
        } else if self.eat_token(&TokenKind::Keyword(KeywordKind::Static))? {
            let base_type = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Declaration(Box::new(base_type), ThinVec::new(), true));
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type.clone(), true)?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Box::new(base_type), declarators, true));
        }

        if self.is_type_name() && self.peek()? != TokenKind::LeftParen {
            let base_type = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Declaration(
                    Box::new(base_type),
                    ThinVec::new(),
                    false,
                ));
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type.clone(), true)?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Box::new(base_type), declarators, false));
        }

        if let TokenKind::Keyword(k) = token.kind {
            if k == KeywordKind::Return {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Return(Box::new(expr)));
            } else if k == KeywordKind::If {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let then = self.parse_stmt()?;
                let else_stmt = self.maybe_start(&TokenKind::Keyword(KeywordKind::Else), |p| {
                    Ok(Box::new(p.parse_stmt()?))
                })?;
                return Ok(Stmt::If(Box::new(cond), Box::new(then), else_stmt));
            } else if k == KeywordKind::While {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let body = self.parse_stmt()?;
                return Ok(Stmt::While(Box::new(cond), Box::new(body)));
            } else if k == KeywordKind::For {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;

                let init = self.maybe_end(&TokenKind::Semicolon, |p| {
                    if p.eat_token(&TokenKind::Keyword(KeywordKind::Static))? {
                        return Err(ParserError::UnexpectedToken(p.current_token()?));
                    }
                    let result = if let Ok(ty) = p.parse_type() {
                        let id = p.expect_name()?;
                        let initializer = p.parse_initializer_expr()?;
                        ForInit::Declaration(ty, id, initializer)
                    } else {
                        ForInit::Expr(p.parse_expr()?)
                    };

                    Ok(Box::new(result))
                })?;

                let cond =
                    self.maybe_end(&TokenKind::Semicolon, |p| Ok(Box::new(p.parse_expr()?)))?;
                let inc =
                    self.maybe_end(&TokenKind::RightParen, |p| Ok(Box::new(p.parse_expr()?)))?;
                let body = self.parse_stmt()?;

                return Ok(Stmt::For(init, cond, inc, Box::new(body)));
            } else if k == KeywordKind::Switch {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Switch(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Case {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Case(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Default {
                self.eat()?;
                self.expect_punct(TokenKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Default(Box::new(stmt)));
            } else if k == KeywordKind::Goto {
                self.eat()?;
                let token = self.current_token()?;
                let id = self.expect_name()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Goto(id, token.span));
            } else if k == KeywordKind::Break {
                return self.parse_simple_statement(Stmt::Break);
            } else if k == KeywordKind::Continue {
                return self.parse_simple_statement(Stmt::Continue);
            } else if k == KeywordKind::Do {
                self.eat()?;
                let body = self.parse_stmt()?;
                self.expect_keyword(KeywordKind::While)?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::DoWhile(Box::new(body), Box::new(cond)));
            } else if k == KeywordKind::Typedef {
                self.eat()?;
                let base_ty = self.parse_type_specifier()?;
                loop {
                    let (ty, name, _) = self.parse_declarator_suffix(base_ty.clone(), true)?;
                    self.typedefs.insert(name, ty);
                    if !self.eat_token(&TokenKind::Comma)? {
                        break;
                    }
                }
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Empty);
            }
        }

        // Check for a label
        let pos = self.position;
        if let Ok(TokenKind::Identifier(id)) = self.current_kind() {
            let token = self.current_token()?;
            self.eat()?;
            if self.eat_token(&TokenKind::Colon)? {
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Label(id, Box::new(stmt), token.span));
            }
            self.position = pos;
        }

        if self.eat_token(&TokenKind::Semicolon)? {
            return Ok(Stmt::Empty);
        }

        let expr = self.parse_expr()?;
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(Stmt::Expr(Box::new(expr)))
    }
    /// Parses a simple statement like Break or Continue.
    fn parse_simple_statement(&mut self, stmt: Stmt) -> Result<Stmt, ParserError> {
        self.eat()?; // eat the keyword
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(stmt)
    }

    /// Parses a function signature.
    fn parse_function_signature(
        &mut self,
        param_name_required: bool,
    ) -> Result<FunctionSignature, ParserError> {
        let mut is_inline = false;
        let mut is_noreturn = false;
        loop {
            if self.eat_token(&TokenKind::Keyword(KeywordKind::Inline))? {
                is_inline = true;
            } else if self.eat_token(&TokenKind::Keyword(KeywordKind::_Noreturn))? {
                is_noreturn = true;
            } else {
                break;
            }
        }

        let ty = self.parse_type()?;
        let id = self.expect_name()?;
        self.expect_punct(TokenKind::LeftParen)?;
        let mut params = ThinVec::new();
        let mut is_variadic = false;
        while self.eat_token(&TokenKind::RightParen)? == false {
            if self.eat_token(&TokenKind::Ellipsis)? {
                is_variadic = true;
                // Expect a closing parenthesis after ...
                self.expect_punct(TokenKind::RightParen)?;
                break;
            }
            let base_type = self.parse_type_specifier()?;
            let declarator = self.parse_declarator(base_type, param_name_required)?;
            params.push(Parameter {
                ty: declarator.ty,
                name: declarator.name,
                span: declarator.span,
            });

            self.eat_token(&TokenKind::Comma)?;
        }
        Ok(FunctionSignature(
            ty,
            id,
            params,
            is_inline,
            is_variadic,
            is_noreturn,
        ))
    }

    /// Parses a function.
    fn parse_function(&mut self) -> Result<Function, ParserError> {
        let FunctionSignature(return_type, name, params, is_inline, is_variadic, is_noreturn) =
            self.parse_function_signature(false)?;
        self.expect_punct(TokenKind::LeftBrace)?;
        let mut stmts = ThinVec::new();
        while self.eat_token(&TokenKind::RightBrace)? == false {
            stmts.push(self.parse_stmt()?);
        }
        Ok(Function {
            return_type,
            name,
            params,
            body: stmts,
            is_inline,
            is_variadic,
            is_noreturn,
        })
    }

    /// Parses the entire program.
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `Program`, or a `ParserError` if parsing fails.
    fn parse_global(&mut self) -> Result<Stmt, ParserError> {
        let pos = self.position;
        if let Ok(FunctionSignature(ty, name, params, is_inline, is_variadic, is_noreturn)) =
            self.parse_function_signature(false)
        {
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::FunctionDeclaration {
                    ty: Box::new(ty),
                    name,
                    params,
                    is_variadic,
                    is_inline,
                    is_noreturn,
                });
            } else {
                let token = self.current_token()?;
                self.position = pos;
                return Err(ParserError::UnexpectedToken(token));
            }
        }
        self.position = pos;

        if self.eat_token(&TokenKind::Keyword(KeywordKind::Typedef))? {
            let base_ty = self.parse_type_specifier()?;
            loop {
                let (ty, name, _) = self.parse_declarator_suffix(base_ty.clone(), true)?;
                self.typedefs.insert(name, ty);
                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Empty);
        }

        let is_static = self.eat_token(&TokenKind::Keyword(KeywordKind::Static))?;
        let base_type = self.parse_type_specifier()?;
        if self.eat_token(&TokenKind::Semicolon)? {
            return Ok(Stmt::Declaration(
                Box::new(base_type),
                ThinVec::new(),
                is_static,
            ));
        }
        let mut declarators = ThinVec::new();
        loop {
            let (ty, name, id_token) = self.parse_declarator_suffix(base_type.clone(), true)?;
            let initializer = self.parse_initializer_expr()?;
            declarators.push(ast::Declarator {
                ty,
                name,
                initializer,
                span: id_token.span,
            });

            if self.eat_token(&TokenKind::Comma)? == false {
                break;
            }
        }
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(Stmt::Declaration(
            Box::new(base_type),
            declarators,
            is_static,
        ))
    }

    pub fn parse(&mut self) -> Result<TranslationUnit, ParserError> {
        let mut globals = ThinVec::new();
        let mut functions = ThinVec::new();
        while let Ok(token) = self.current_token()
            && token.kind != TokenKind::Eof
        {
            let pos = self.position;
            if self.parse_global().is_ok() {
                self.position = pos;
                globals.push(self.parse_global()?);
            } else {
                self.position = pos;
                functions.push(self.parse_function()?);
            }
        }
        Ok(TranslationUnit { globals, functions })
    }

    /// parse a option action when start token is found
    fn maybe_start<T, F>(
        &mut self,
        start_token: &TokenKind,
        mut parse_fn: F,
    ) -> Result<Option<T>, ParserError>
    where
        F: FnMut(&mut Self) -> Result<T, ParserError>,
    {
        if self.eat_token(start_token)? {
            let item = parse_fn(self)?;
            Ok(Some(item))
        } else {
            Ok(None)
        }
    }

    /// Parses a optional action
    fn maybe_end<T, F>(
        &mut self,
        end_token: &TokenKind,
        mut parse_fn: F,
    ) -> Result<Option<T>, ParserError>
    where
        F: FnMut(&mut Self) -> Result<T, ParserError>,
    {
        if self.eat_token(end_token)? {
            Ok(None)
        } else {
            let item = parse_fn(self)?;
            self.expect_punct(end_token.clone())?;

            Ok(Some(item))
        }
    }

    /// Parses a delimited list of items.
    fn parse_delimited_list<T, F>(
        &mut self,
        start_token: TokenKind,
        end_token: TokenKind,
        separator: TokenKind,
        mut parse_item: F,
    ) -> Result<ThinVec<T>, ParserError>
    where
        F: FnMut(&mut Self) -> Result<T, ParserError>,
    {
        self.expect_punct(start_token)?;
        let mut items = ThinVec::new();
        if self.eat_token(&end_token)? {
            return Ok(items);
        }
        loop {
            items.push(parse_item(self)?);
            if self.eat_token(&end_token)? {
                break;
            }
            self.expect_punct(separator.clone())?;
            if self.eat_token(&end_token)? {
                break;
            }
        }
        Ok(items)
    }

    /// Parses a `_Static_assert` declaration.
    fn parse_static_assert(&mut self) -> Result<Stmt, ParserError> {
        self.eat()?; // consume `_Static_assert`
        self.expect_punct(TokenKind::LeftParen)?;
        let expr = self.parse_expr()?;
        self.expect_punct(TokenKind::Comma)?;
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::String(s) => {
                self.eat()?;
                self.expect_punct(TokenKind::RightParen)?;
                self.expect_punct(TokenKind::Semicolon)?;
                Ok(Stmt::StaticAssert(Box::new(expr), s))
            }
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }
}
