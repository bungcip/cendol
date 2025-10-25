use crate::parser::ast::{Expr, ForInit, Function, Parameter, Program, Stmt, Type};
use crate::parser::error::ParserError;
use crate::parser::token::{KeywordKind, Token, TokenKind};
use crate::preprocessor;
use std::collections::HashSet;

pub mod ast;
pub mod error;
pub mod token;

/// A parser that converts a stream of tokens into an abstract syntax tree.
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    typedefs: HashSet<String>,
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
            filtered_tokens.push(token.into());
        }

        let parser = Parser {
            tokens: filtered_tokens,
            position: 0,
            typedefs: HashSet::new(),
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

    /// Consumes the current token.
    fn eat(&mut self) -> Result<(), ParserError> {
        self.position += 1;
        Ok(())
    }

    /// Expects a specific punctuation token.
    fn expect_punct(&mut self, value: TokenKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if token.kind == value {
            self.eat()?;
            return Ok(());
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    /// Expects a specific keyword.
    fn expect_keyword(&mut self, value: KeywordKind) -> Result<(), ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone()
            && k == value
        {
            self.eat()?;
            return Ok(());
        }
        Err(ParserError::UnexpectedToken(token.clone()))
    }

    /// Peeks if the current token sequence is a type name without consuming tokens.
    fn is_type_name(&mut self) -> bool {
        let original_pos = self.position;
        let result = self.parse_type().is_ok();
        self.position = original_pos;
        result
    }

    /// Parses a type specifier (e.g., `int`, `struct S`, `long long`).
    fn parse_type_specifier(&mut self) -> Result<Type, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == KeywordKind::Const {
                self.eat()?;
                return self.parse_type_specifier();
            }
            match k {
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
                KeywordKind::Int => {
                    self.eat()?;
                    Ok(Type::Int)
                }
                KeywordKind::Char => {
                    self.eat()?;
                    Ok(Type::Char)
                }
                KeywordKind::Float => {
                    self.eat()?;
                    Ok(Type::Float)
                }
                KeywordKind::Double => {
                    self.eat()?;
                    Ok(Type::Double)
                }
                KeywordKind::Void => {
                    self.eat()?;
                    Ok(Type::Void)
                }
                KeywordKind::Bool => {
                    self.eat()?;
                    Ok(Type::Bool)
                }
                KeywordKind::Struct => {
                    self.eat()?;
                    let name = if let Ok(token) = self.current_token() {
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            Some(id)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let Ok(token) = self.current_token() {
                        if let TokenKind::LeftBrace = token.kind {
                            self.eat()?;
                            let mut members = Vec::new();
                            while let Ok(t) = self.current_token() {
                                if let TokenKind::RightBrace = t.kind {
                                    self.eat()?;
                                    break;
                                }
                                let ty = self.parse_type_specifier()?; // Use parse_type_specifier here
                                let mut current_ty = ty;
                                // Handle pointer declarators for struct members
                                while let Ok(t) = self.current_token() {
                                    if let TokenKind::Star = t.kind {
                                        self.eat()?;
                                        current_ty = Type::Pointer(Box::new(current_ty));
                                    } else {
                                        break;
                                    }
                                }
                                let token = self.current_token()?;
                                if let TokenKind::Identifier(id) = token.kind.clone() {
                                    self.eat()?;
                                    members.push(Parameter { ty: current_ty, name: id });
                                }
                                self.expect_punct(TokenKind::Semicolon)?;
                            }
                            Ok(Type::Struct(name, members))
                        } else if let Some(name) = name {
                            Ok(Type::Struct(Some(name), Vec::new()))
                        } else {
                            Err(ParserError::UnexpectedToken(token))
                        }
                    } else {
                        Err(ParserError::UnexpectedEof)
                    }
                }
                KeywordKind::Union => {
                    self.eat()?;
                    let name = if let Ok(token) = self.current_token() {
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            Some(id)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let Ok(token) = self.current_token() {
                        if let TokenKind::LeftBrace = token.kind {
                            self.eat()?;
                            let mut members = Vec::new();
                            while let Ok(t) = self.current_token() {
                                if let TokenKind::RightBrace = t.kind {
                                    self.eat()?;
                                    break;
                                }
                                let ty = self.parse_type_specifier()?; // Use parse_type_specifier here
                                let mut current_ty = ty;
                                // Handle pointer declarators for union members
                                while let Ok(t) = self.current_token() {
                                    if let TokenKind::Star = t.kind {
                                        self.eat()?;
                                        current_ty = Type::Pointer(Box::new(current_ty));
                                    } else {
                                        break;
                                    }
                                }
                                let token = self.current_token()?;
                                if let TokenKind::Identifier(id) = token.kind.clone() {
                                    self.eat()?;
                                    members.push(Parameter { ty: current_ty, name: id });
                                }
                                self.expect_punct(TokenKind::Semicolon)?;
                            }
                            Ok(Type::Union(name, members))
                        } else if let Some(name) = name {
                            Ok(Type::Union(Some(name), Vec::new()))
                        } else {
                            Err(ParserError::UnexpectedToken(token))
                        }
                    } else {
                        Err(ParserError::UnexpectedEof)
                    }
                }
                KeywordKind::Enum => {
                    self.eat()?;
                    // Optional identifier for enum tag
                    let _name = if let Ok(token) = self.current_token() {
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            Some(id)
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    self.expect_punct(TokenKind::LeftBrace)?;
                    let mut enumerators = Vec::new();
                    while let Ok(t) = self.current_token() {
                        if let TokenKind::RightBrace = t.kind {
                            self.eat()?;
                            break;
                        }
                        let token = self.current_token()?;
                        if let TokenKind::Identifier(id) = token.kind.clone() {
                            self.eat()?;
                            enumerators.push(id);
                        }
                        // Handle optional assignment for enum values
                        if let Ok(t) = self.current_token()
                            && let TokenKind::Equal = t.kind
                        {
                            self.eat()?;
                            self.parse_expr()?; // Consume the expression for the enum value
                        }
                        if let Ok(t) = self.current_token()
                            && let TokenKind::Comma = t.kind
                        {
                            self.eat()?;
                        }
                    }
                    Ok(Type::Enum(enumerators))
                }
                _ => Err(ParserError::UnexpectedToken(token)),
            }
        } else if self.typedefs.contains(&token.to_string()) {
            self.eat()?;
            Ok(Type::Typedef(token.to_string()))
        }
        else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses declarator suffixes (pointers and arrays) and returns the final type and identifier.
    /// This function assumes the base type has already been parsed.
    fn parse_declarator_suffix(&mut self, base_type: Type) -> Result<(Type, String), ParserError> {
        let mut ty = base_type;
        // Parse pointers
        while let Ok(token) = self.current_token() {
            if let TokenKind::Star = token.kind {
                self.eat()?;
                ty = Type::Pointer(Box::new(ty));
            } else {
                break;
            }
        }

        let token = self.current_token()?;
        let id = if let TokenKind::Identifier(id) = token.kind.clone() {
            self.eat()?;
            id
        } else {
            return Err(ParserError::UnexpectedToken(token));
        };

        // Parse array dimensions
        while let Ok(token) = self.current_token() {
            if let TokenKind::LeftBracket = token.kind {
                self.eat()?;
                if self.current_token()?.kind == TokenKind::RightBracket {
                    self.eat()?;
                    ty = Type::Array(Box::new(ty), 0); // Unsized array
                } else {
                    let size_expr = self.parse_expr()?;
                    let size = if let Expr::Number(n) = size_expr {
                        n as usize
                    } else {
                        return Err(ParserError::UnexpectedToken(token));
                    };
                    self.expect_punct(TokenKind::RightBracket)?;
                    ty = Type::Array(Box::new(ty), size);
                }
            } else {
                break;
            }
        }
        Ok((ty, id))
    }

    /// Parses a type. This function now orchestrates `parse_type_specifier` and `parse_declarator_suffix`.
    fn parse_type(&mut self) -> Result<Type, ParserError> {
        let base_type = self.parse_type_specifier()?;
        // For abstract declarators (e.g., `int *`), there might not be an identifier immediately.
        // This function is primarily for parsing a full type with a declarator.
        // If we are just parsing a type for a cast or sizeof, we might not have an identifier.
        // The `is_type_name` function will handle backtracking if no identifier is found.
        let original_pos = self.position;
        if let Ok(token) = self.current_token() {
            if token.kind == TokenKind::Star || token.kind == TokenKind::LeftBracket {
                if let Ok((ty, _)) = self.parse_declarator_suffix(base_type.clone()) {
                    return Ok(ty);
                }
            }
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
            TokenKind::LessThan | TokenKind::GreaterThan | TokenKind::LessThanEqual | TokenKind::GreaterThanEqual => Some((15, 16)),
            TokenKind::LessThanLessThan | TokenKind::GreaterThanGreaterThan => Some((17, 18)),
            TokenKind::Plus | TokenKind::Minus => Some((19, 20)),
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Some((21, 22)),
            TokenKind::Arrow | TokenKind::Dot => Some((23, 24)),
            TokenKind::Equal | TokenKind::PlusEqual | TokenKind::MinusEqual | TokenKind::AsteriskEqual | TokenKind::SlashEqual | TokenKind::PercentEqual | TokenKind::LessThanLessThanEqual | TokenKind::GreaterThanGreaterThanEqual | TokenKind::AmpersandEqual | TokenKind::CaretEqual | TokenKind::PipeEqual => Some((4, 3)),
            _ => None,
        }
    }
 
    /// Parses an expression using the Pratt parsing algorithm.
    fn parse_pratt_expr(&mut self, min_bp: u8) -> Result<Expr, ParserError> {
        let mut lhs =
            if let Some(((), r_bp)) = self.prefix_binding_power(&self.current_token()?.kind) {
                let token = self.current_token()?;
                self.eat()?;
                match token.kind {
                    TokenKind::PlusPlus => {
                        let rhs = self.parse_pratt_expr(r_bp)?;
                        Expr::Increment(Box::new(rhs))
                    }
                    TokenKind::MinusMinus => {
                        let rhs = self.parse_pratt_expr(r_bp)?;
                        Expr::Decrement(Box::new(rhs))
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
                        if self.current_token()?.kind == TokenKind::LeftParen {
                            self.eat()?; // consume (
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
                    _ => unreachable!(),
                }
            } else {
                self.parse_primary()?
            };

        loop {
            let token = self.current_token()?;
            if let Some((l_bp, ())) = self.postfix_binding_power(&token.kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;

                lhs = match token.kind {
                    TokenKind::PlusPlus => Expr::Increment(Box::new(lhs)),
                    TokenKind::MinusMinus => Expr::Decrement(Box::new(lhs)),
                    _ => unreachable!(),
                };
                continue;
            }
            if let Some((l_bp, r_bp)) = self.infix_binding_power(&token.kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;
                let rhs = self.parse_pratt_expr(r_bp)?;

                lhs = match token.kind {
                    TokenKind::Comma => Expr::Comma(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Equal => Expr::Assign(Box::new(lhs), Box::new(rhs)),
                    TokenKind::PlusEqual => Expr::AssignAdd(Box::new(lhs), Box::new(rhs)),
                    TokenKind::MinusEqual => Expr::AssignSub(Box::new(lhs), Box::new(rhs)),
                    TokenKind::AsteriskEqual => Expr::AssignMul(Box::new(lhs), Box::new(rhs)),
                    TokenKind::SlashEqual => Expr::AssignDiv(Box::new(lhs), Box::new(rhs)),
                    TokenKind::PercentEqual => Expr::AssignMod(Box::new(lhs), Box::new(rhs)),
                    TokenKind::LessThanLessThanEqual => {
                        Expr::AssignLeftShift(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::GreaterThanGreaterThanEqual => {
                        Expr::AssignRightShift(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::AmpersandEqual => {
                        Expr::AssignBitwiseAnd(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::CaretEqual => Expr::AssignBitwiseXor(Box::new(lhs), Box::new(rhs)),
                    TokenKind::PipeEqual => Expr::AssignBitwiseOr(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Plus => Expr::Add(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Minus => Expr::Sub(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Star => Expr::Mul(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Slash => Expr::Div(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Percent => Expr::Mod(Box::new(lhs), Box::new(rhs)),
                    TokenKind::EqualEqual => Expr::Equal(Box::new(lhs), Box::new(rhs)),
                    TokenKind::BangEqual => Expr::NotEqual(Box::new(lhs), Box::new(rhs)),
                    TokenKind::LessThan => Expr::LessThan(Box::new(lhs), Box::new(rhs)),
                    TokenKind::GreaterThan => Expr::GreaterThan(Box::new(lhs), Box::new(rhs)),
                    TokenKind::LessThanEqual => {
                        Expr::LessThanOrEqual(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::GreaterThanEqual => {
                        Expr::GreaterThanOrEqual(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::AmpersandAmpersand => {
                        Expr::LogicalAnd(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::PipePipe => Expr::LogicalOr(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Pipe => Expr::BitwiseOr(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Caret => Expr::BitwiseXor(Box::new(lhs), Box::new(rhs)),
                    TokenKind::Ampersand => Expr::BitwiseAnd(Box::new(lhs), Box::new(rhs)),
                    TokenKind::LessThanLessThan => Expr::LeftShift(Box::new(lhs), Box::new(rhs)),
                    TokenKind::GreaterThanGreaterThan => {
                        Expr::RightShift(Box::new(lhs), Box::new(rhs))
                    }
                    TokenKind::Arrow => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::PointerMember(Box::new(lhs), name)
                        } else {
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    TokenKind::Dot => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::Member(Box::new(lhs), name)
                        } else {
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    _ => unreachable!(),
                };
                continue;
            }
            if let TokenKind::Question = token.kind {
                let l_bp = 2;
                if l_bp < min_bp {
                    break;
                }
                self.eat()?; // Consume '?'
                let then_expr = self.parse_pratt_expr(0)?;
                self.expect_punct(TokenKind::Colon)?;
                let else_expr = self.parse_pratt_expr(l_bp - 1)?;
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
                // Strip suffixes like L, U, LL, UU
                let num_str =
                    n.trim_end_matches(|c: char| c == 'L' || c == 'U' || c == 'l' || c == 'u');
                Ok(Expr::Number(num_str.parse().unwrap()))
            }
            TokenKind::String(s) => {
                self.eat()?;
                Ok(Expr::String(s))
            }
            TokenKind::Char(s) => {
                self.eat()?;
                Ok(Expr::Char(s))
            }
            TokenKind::Identifier(name) => {
                self.eat()?;
                let mut expr = Expr::Variable(name, token.span.clone());
                while let Ok(token) = self.current_token() {
                    match token.kind {
                        TokenKind::PlusPlus => {
                            self.eat()?;
                            expr = Expr::Increment(Box::new(expr));
                        }
                        TokenKind::MinusMinus => {
                            self.eat()?;
                            expr = Expr::Decrement(Box::new(expr));
                        }
                        TokenKind::LeftParen => {
                            let location = token.span.clone();
                            let token_for_error = token.clone();
                            self.eat()?; // consume '('
                            let mut args = Vec::new();
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
                let expr = self.parse_primary()?;
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

                    if self.current_token().is_ok()
                        && self.current_token()?.kind == TokenKind::LeftBrace
                    {
                        // Compound Literal: (type){...}
                        let initializers = self.parse_initializer_list()?;
                        Ok(Expr::CompoundLiteral(Box::new(param_ty), initializers))
                    } else {
                        // Cast: (type)expr
                        let expr = self.parse_pratt_expr(15)?; // High precedence for cast's operand
                        Ok(Expr::Cast(Box::new(param_ty), Box::new(expr)))
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
                Ok(Expr::StructInitializer(initializers))
            }
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }

    fn parse_designator(&mut self) -> Result<Expr, ParserError> {
        self.eat()?; // consume .
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind.clone() {
            self.eat()?;
            self.expect_punct(TokenKind::Equal)?;
            let expr = self.parse_expr()?;
            Ok(Expr::DesignatedInitializer(id, Box::new(expr)))
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses an initializer list.
    fn parse_initializer_list(&mut self) -> Result<Vec<Expr>, ParserError> {
        self.expect_punct(TokenKind::LeftBrace)?;
        let mut initializers = Vec::new();

        // Handle empty initializer list: {}
        if self.current_token()?.kind == TokenKind::RightBrace {
            self.eat()?;
            return Ok(initializers);
        }

        loop {
            // Parse one initializer expression (either designated or normal)
            if self.current_token()?.kind == TokenKind::Dot {
                initializers.push(self.parse_designator()?);
            } else {
                initializers.push(self.parse_expr()?);
            }

            // After an initializer, expect a comma or a closing brace
            let token = self.current_token()?;
            if token.kind == TokenKind::Comma {
                self.eat()?;
                // If a comma is followed by a brace, it's a trailing comma.
                if self.current_token()?.kind == TokenKind::RightBrace {
                    self.eat()?;
                    break;
                }
            } else if token.kind == TokenKind::RightBrace {
                self.eat()?;
                break;
            } else {
                // Any other token is an error.
                return Err(ParserError::UnexpectedToken(token));
            }
        }
        Ok(initializers)
    }

    /// Parses a statement.
    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::LeftBrace = token.kind.clone() {
            self.eat()?;
            let mut stmts = Vec::new();
            while let Ok(t) = self.current_token() {
                if let TokenKind::RightBrace = t.kind {
                    self.eat()?;
                    break;
                }
                stmts.push(self.parse_stmt()?);
            }
            return Ok(Stmt::Block(stmts));
        } else if let Ok(base_type) = self.parse_type_specifier() {
            let mut declarators = Vec::new();
            loop {
                let (ty, name) = self.parse_declarator_suffix(base_type.clone())?;

                let mut initializer = None;
                if let Ok(t) = self.current_token()
                    && let TokenKind::Equal = t.kind
                {
                    self.eat()?;
                    initializer = Some(Box::new(self.parse_expr()?));
                }
                declarators.push(ast::Declarator {
                    ty,
                    name,
                    initializer,
                });

                if let Ok(t) = self.current_token()
                    && let TokenKind::Comma = t.kind
                {
                    self.eat()?;
                } else {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(base_type, declarators));
        } else if let TokenKind::Keyword(k) = token.kind.clone() {
            if k == KeywordKind::Return {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Return(expr));
            } else if k == KeywordKind::If {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let then = self.parse_stmt()?;
                let mut else_stmt = None;
                let next_token = self.current_token()?;
                if let TokenKind::Keyword(k) = next_token.kind.clone()
                    && k == KeywordKind::Else
                {
                    self.eat()?;
                    else_stmt = Some(Box::new(self.parse_stmt()?));
                }
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
                let init = if self.current_token()?.kind == TokenKind::Semicolon {
                    self.eat()?; // consume ;
                    None
                } else if let Ok(ty) = self.parse_type() {
                    let token = self.current_token()?;
                    if let TokenKind::Identifier(id) = token.kind.clone() {
                        self.eat()?;
                        let mut initializer = None;
                        if let Ok(t) = self.current_token()
                            && let TokenKind::Equal = t.kind
                        {
                            self.eat()?;
                            initializer = Some(Box::new(self.parse_expr()?));
                        }
                        Some(ForInit::Declaration(ty, id, initializer))
                    } else {
                        return Err(ParserError::UnexpectedToken(token));
                    }
                } else {
                    Some(ForInit::Expr(self.parse_expr()?))
                };

                // Optional ; for cond
                if self.current_token()?.kind == TokenKind::Semicolon {
                    self.eat()?; // consume ;
                }
                let cond = if self.current_token()?.kind == TokenKind::Semicolon {
                    self.eat()?; // consume ;
                    None
                } else {
                    Some(Box::new(self.parse_expr()?))
                };

                // Optional ; for inc
                if self.current_token()?.kind == TokenKind::Semicolon {
                    self.eat()?; // consume ;
                }
                let inc = if self.current_token()?.kind == TokenKind::RightParen {
                    self.eat()?; // consume )
                    None
                } else {
                    let result = self.parse_expr()?;
                    self.expect_punct(TokenKind::RightParen)?;
                    Some(Box::new(result))
                };

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
                if let TokenKind::Identifier(id) = token.kind.clone() {
                    self.eat()?;
                    self.expect_punct(TokenKind::Semicolon)?;
                    return Ok(Stmt::Goto(id));
                }
            } else if k == KeywordKind::Break {
                self.eat()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Break);
            } else if k == KeywordKind::Continue {
                self.eat()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Continue);
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
                let ty = self.parse_type()?;
                let token = self.current_token()?;
                if let TokenKind::Identifier(id) = token.kind.clone() {
                    self.eat()?;
                    self.typedefs.insert(id.clone());
                    self.expect_punct(TokenKind::Semicolon)?;
                    return Ok(Stmt::Typedef(ty, id));
                }
            }
        }

        if let TokenKind::Semicolon = token.kind {
            self.eat()?;
            return Ok(Stmt::Empty);
        }

        let expr = self.parse_expr()?;
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(Stmt::Expr(expr))
    }

    /// Parses a function signature.
    fn parse_function_signature(
        &mut self,
    ) -> Result<(Type, String, Vec<Parameter>, bool, bool), ParserError> {
        let mut is_inline = false;
        // Check for inline keyword before return type
        if let Ok(token) = self.current_token() {
            if let TokenKind::Keyword(KeywordKind::Inline) = token.kind {
                self.eat()?;
                is_inline = true;
            }
        }
        let ty = self.parse_type()?;
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind.clone() {
            self.eat()?;
            self.expect_punct(TokenKind::LeftParen)?;
            let mut params = Vec::new();
            let mut is_variadic = false;
            while let Ok(t) = self.current_token() {
                if let TokenKind::RightParen = t.kind {
                    self.eat()?;
                    break;
                }
                if let TokenKind::Ellipsis = t.kind {
                    self.eat()?;
                    is_variadic = true;
                    // Expect a closing parenthesis after ...
                    self.expect_punct(TokenKind::RightParen)?;
                    break;
                }
                let base_type = self.parse_type_specifier()?;
                let (param_ty, id) = self.parse_declarator_suffix(base_type)?;
                params.push(Parameter { ty: param_ty, name: id });

                if let Ok(t) = self.current_token()
                    && let TokenKind::Comma = t.kind
                {
                    self.eat()?;
                }
            }
            Ok((ty, id, params, is_inline, is_variadic))
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses a function.
    fn parse_function(&mut self) -> Result<Function, ParserError> {
        let (return_type, name, params, is_inline, is_variadic) =
            self.parse_function_signature()?;
        self.expect_punct(TokenKind::LeftBrace)?;
        let mut stmts = Vec::new();
        while let Ok(t) = self.current_token() {
            if let TokenKind::RightBrace = t.kind {
                self.eat()?;
                break;
            }
            stmts.push(self.parse_stmt()?);
        }
        Ok(Function {
            return_type,
            name,
            params,
            body: stmts,
            is_inline,
            is_variadic,
        })
    }

    /// Parses the entire program.
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `Program`, or a `ParserError` if parsing fails.
    fn parse_global(&mut self) -> Result<Stmt, ParserError> {
        let pos = self.position;
        if let Ok((ty, id, params, _is_inline, is_variadic)) = self.parse_function_signature() {
            let token = self.current_token()?;
            if let TokenKind::Semicolon = token.kind {
                self.eat()?;
                return Ok(Stmt::FunctionDeclaration(ty, id, params, is_variadic));
            } else {
                self.position = pos;
                return Err(ParserError::UnexpectedToken(token));
            }
        }
        self.position = pos;

        let base_type = self.parse_type_specifier()?;
        let mut declarators = Vec::new();
        loop {
            let (ty, name) = self.parse_declarator_suffix(base_type.clone())?;

            let mut initializer = None;
            if let Ok(t) = self.current_token()
                && let TokenKind::Equal = t.kind
            {
                self.eat()?;
                initializer = Some(Box::new(self.parse_expr()?));
            }
            declarators.push(ast::Declarator {
                ty,
                name,
                initializer,
            });

            if let Ok(t) = self.current_token()
                && let TokenKind::Comma = t.kind
            {
                self.eat()?;
            } else {
                break;
            }
        }
        self.expect_punct(TokenKind::Semicolon)?;
        return Ok(Stmt::Declaration(base_type, declarators));
    }

    pub fn parse(&mut self) -> Result<Program, ParserError> {
        let mut globals = Vec::new();
        let mut functions = Vec::new();
        while self.current_token().is_ok() && !matches!(self.current_token()?.kind, TokenKind::Eof)
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
        Ok(Program { globals, functions })
    }
}
