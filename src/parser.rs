use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, ParseError};
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::{debug, trace};
use std::cell::Cell;
use std::collections::HashSet;
use symbol_table::GlobalSymbol as Symbol;

// ParseError is now defined in diagnostic.rs

/// Binding power for Pratt parser operator precedence
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindingPower(u8);

impl BindingPower {
    pub const MIN: Self = Self(0);
    pub const ASSIGNMENT: Self = Self(10);
    pub const CONDITIONAL: Self = Self(20);
    pub const LOGICAL_OR: Self = Self(30);
    pub const LOGICAL_AND: Self = Self(40);
    pub const BITWISE_OR: Self = Self(50);
    pub const BITWISE_XOR: Self = Self(60);
    pub const BITWISE_AND: Self = Self(70);
    pub const EQUALITY: Self = Self(80);
    pub const RELATIONAL: Self = Self(90);
    pub const SHIFT: Self = Self(100);
    pub const ADDITIVE: Self = Self(110);
    pub const MULTIPLICATIVE: Self = Self(120);
    pub const CAST: Self = Self(130);
    pub const UNARY: Self = Self(140);
    pub const POSTFIX: Self = Self(150);
    pub const PRIMARY: Self = Self(160);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
}

/// Pratt parser implementation
pub struct PrattParser;

impl PrattParser {
    pub fn get_binding_power(token_kind: TokenKind) -> Option<(BindingPower, Associativity)> {
        match token_kind {
            // Assignment operators (right-associative)
            TokenKind::Assign
            | TokenKind::PlusAssign
            | TokenKind::MinusAssign
            | TokenKind::StarAssign
            | TokenKind::DivAssign
            | TokenKind::ModAssign
            | TokenKind::AndAssign
            | TokenKind::OrAssign
            | TokenKind::XorAssign
            | TokenKind::LeftShiftAssign
            | TokenKind::RightShiftAssign => Some((BindingPower::ASSIGNMENT, Associativity::Right)),

            // Comma operator (left-associative, lowest precedence)
            TokenKind::Comma => Some((BindingPower(5), Associativity::Left)),

            // Conditional operator (right-associative)
            TokenKind::Question => Some((BindingPower::CONDITIONAL, Associativity::Right)),

            // Logical operators (left-associative)
            TokenKind::LogicOr => Some((BindingPower::LOGICAL_OR, Associativity::Left)),
            TokenKind::LogicAnd => Some((BindingPower::LOGICAL_AND, Associativity::Left)),

            // Bitwise operators (left-associative)
            TokenKind::Or => Some((BindingPower::BITWISE_OR, Associativity::Left)),
            TokenKind::Xor => Some((BindingPower::BITWISE_XOR, Associativity::Left)),
            TokenKind::And => Some((BindingPower::BITWISE_AND, Associativity::Left)),

            // Comparison operators (left-associative)
            TokenKind::Equal | TokenKind::NotEqual => {
                Some((BindingPower::EQUALITY, Associativity::Left))
            }
            TokenKind::Less
            | TokenKind::Greater
            | TokenKind::LessEqual
            | TokenKind::GreaterEqual => Some((BindingPower::RELATIONAL, Associativity::Left)),

            // Shift operators (left-associative)
            TokenKind::LeftShift | TokenKind::RightShift => {
                Some((BindingPower::SHIFT, Associativity::Left))
            }

            // Additive operators (left-associative)
            TokenKind::Plus | TokenKind::Minus => {
                Some((BindingPower::ADDITIVE, Associativity::Left))
            }

            // Multiplicative operators (left-associative)
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => {
                Some((BindingPower::MULTIPLICATIVE, Associativity::Left))
            }

            // Postfix operators
            TokenKind::Increment
            | TokenKind::Decrement
            | TokenKind::LeftParen
            | TokenKind::LeftBracket
            | TokenKind::Dot
            | TokenKind::Arrow => Some((BindingPower::POSTFIX, Associativity::Left)),

            _ => None,
        }
    }
}

/// Error recovery point for backtracking
#[derive(Debug)]
pub struct ErrorRecoveryPoint {
    pub token_index: usize,
    pub context: String,
}

/// Main parser structure
pub struct Parser<'arena, 'src> {
    tokens: &'src [Token],
    current_idx: usize,
    ast: &'arena mut Ast,
    diag: &'src mut DiagnosticEngine,

    // Parsing context
    #[allow(unused)]
    in_function_body: bool,
    #[allow(unused)]
    in_struct_declaration: bool,
    #[allow(unused)]
    in_enum_declaration: bool,

    // Error recovery state
    #[allow(unused)]
    error_recovery_points: Vec<ErrorRecoveryPoint>,

    // Typedef symbol table for disambiguation
    typedef_names: HashSet<Symbol>,
}

/// Result of parsing an expression
#[derive(Debug)]
pub enum ParseExprOutput {
    Expression(NodeRef),
    Declaration(NodeRef), // For cases where we parse a declaration instead
}

/// Helper enum for reconstructing complex declarators
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
}

impl<'arena, 'src> Parser<'arena, 'src> {
    /// Create a new parser
    pub fn new(
        tokens: &'src [Token],
        ast: &'arena mut Ast,
        diag: &'src mut DiagnosticEngine,
    ) -> Self {
        let mut typedef_names = HashSet::new();
        // Add builtin typedefs
        typedef_names.insert(Symbol::new("va_list"));
        typedef_names.insert(Symbol::new("size_t"));
        typedef_names.insert(Symbol::new("ptrdiff_t"));
        typedef_names.insert(Symbol::new("int8_t"));
        typedef_names.insert(Symbol::new("int16_t"));
        typedef_names.insert(Symbol::new("int32_t"));
        typedef_names.insert(Symbol::new("int64_t"));
        typedef_names.insert(Symbol::new("uint8_t"));
        typedef_names.insert(Symbol::new("uint16_t"));
        typedef_names.insert(Symbol::new("uint32_t"));
        typedef_names.insert(Symbol::new("uint64_t"));
        typedef_names.insert(Symbol::new("intptr_t"));
        typedef_names.insert(Symbol::new("uintptr_t"));

        Parser {
            tokens,
            current_idx: 0,
            ast,
            diag,
            in_function_body: false,
            in_struct_declaration: false,
            in_enum_declaration: false,
            error_recovery_points: Vec::new(),
            typedef_names,
        }
    }

    /// Get the current token (returns None if at end of input)
    fn try_current_token(&self) -> Option<Token> {
        self.tokens.get(self.current_idx).cloned()
    }

    /// Get the current token (returns error if at end of input)
    fn current_token(&self) -> Result<Token, ParseError> {
        self.try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })
    }

    /// Get the current token kind
    fn current_token_kind(&self) -> Option<TokenKind> {
        self.try_current_token().map(|t| t.kind)
    }

    /// Get the current token location
    fn current_token_span(&self) -> Result<SourceSpan, ParseError> {
        Ok(self.current_token()?.location)
    }

    /// Peek at the next token without consuming it
    fn peek_token(&self, next_index: u32) -> Option<&Token> {
        self.tokens.get(self.current_idx + 1 + next_index as usize)
    }

    /// Advance to the next token and return previous token
    fn advance(&mut self) -> Option<Token> {
        if self.current_idx < self.tokens.len() {
            let token = &self.tokens[self.current_idx];
            self.current_idx += 1;
            Some(*token)
        } else {
            None
        }
    }

    /// accept a specific, if found consume it and return it, otherwise nothing happen
    fn accept(&mut self, accepted: TokenKind) -> Option<Token> {
        if self.current_token_kind() == Some(accepted) {
            self.advance()
        } else {
            None
        }
    }

    /// Expect a specific token kind, consume it if found
    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParseError> {
        if let Some(token) = self.try_current_token() {
            if token.kind == expected {
                self.advance().ok_or_else(|| ParseError::SyntaxError {
                    message: "Unexpected end of input".to_string(),
                    location: token.location,
                })?;
                Ok(token)
            } else {
                Err(ParseError::UnexpectedToken {
                    expected: vec![expected],
                    found: token.kind,
                    location: token.location,
                })
            }
        } else {
            Err(ParseError::MissingToken {
                expected,
                location: SourceSpan::empty(),
            })
        }
    }

    /// Check if current token matches any of the given kinds
    fn matches(&self, kinds: &[TokenKind]) -> bool {
        self.current_token_kind()
            .map(|k| kinds.contains(&k))
            .unwrap_or(false)
    }

    /// Skip tokens until we find a synchronization point
    fn synchronize(&mut self) {
        let mut brace_depth = 0;
        let mut paren_depth = 0;
        let mut any_advance = false;

        while let Some(token) = self.try_current_token() {
            match token.kind {
                TokenKind::LeftBrace => {
                    brace_depth += 1;
                    self.advance();
                    any_advance = true;
                }
                TokenKind::RightBrace => {
                    brace_depth -= 1;
                    self.advance();
                    any_advance = true;
                    if brace_depth < 0 {
                        break; // Unmatched brace, stop here
                    }
                }
                TokenKind::LeftParen => {
                    paren_depth += 1;
                    self.advance();
                    any_advance = true;
                }
                TokenKind::RightParen => {
                    paren_depth -= 1;
                    self.advance();
                    any_advance = true;
                    if paren_depth < 0 {
                        break; // Unmatched paren, stop here
                    }
                }
                TokenKind::Semicolon => {
                    self.advance();
                    any_advance = true;
                    if brace_depth == 0 && paren_depth == 0 {
                        break;
                    }
                }
                TokenKind::EndOfFile => {
                    self.advance();
                    any_advance = true;
                    break;
                }
                _ => {
                    self.advance();
                    any_advance = true;
                }
            }
        }

        // If we didn't advance at all, force advance to avoid infinite loop
        if !any_advance {
            self.advance();
        }
    }

    /// Parse C11 floating-point literal syntax
    fn parse_c11_float_literal(&self, text: Symbol) -> Result<f64, ParseError> {
        let text_str = text.as_str();
        let token = self.try_current_token().unwrap();

        // C11 floating-point literal format:
        // [digits][.digits][e|E[+|-]digits][f|F|l|L]
        // or [digits][e|E[+|-]digits][f|F|l|L]
        // or 0[xX][hexdigits][.hexdigits][p|P[+|-]digits][f|F|l|L]

        // Strip suffix (f, F, l, L) for parsing
        let text_without_suffix = if text_str.ends_with('f') || text_str.ends_with('F') ||
                                   text_str.ends_with('l') || text_str.ends_with('L') {
            &text_str[..text_str.len() - 1]
        } else {
            text_str
        };

        // Handle hexadecimal floating-point literals (C99/C11)
        if text_str.starts_with("0x") || text_str.starts_with("0X") {
            self.parse_hex_float_literal(text_without_suffix, token.location)
        } else {
            // Use Rust's built-in parsing for decimal floats
            match text_without_suffix.parse::<f64>() {
                Ok(val) => Ok(val),
                Err(_) => Err(ParseError::SyntaxError {
                    message: format!("Invalid floating-point constant: {}", text_str),
                    location: token.location,
                }),
            }
        }
    }

    /// Parse hexadecimal floating-point literal (C99/C11)
    fn parse_hex_float_literal(&self, text: &str, location: SourceSpan) -> Result<f64, ParseError> {
        // Format: 0[xX][hexdigits][.hexdigits][pP[+|-]digits][fFlL]
        // Example: 0x1.2p3, 0x1p-5f, 0x.8p10L

        let mut chars = text.chars().peekable();
        let mut result = 0.0f64;
        let mut exponent = 0i32;
        let _is_negative = false;
        let mut seen_dot = false;
        let mut fraction_digits = 0;

        // Skip "0x" or "0X"
        chars.next(); // '0'
        chars.next(); // 'x' or 'X'

        // Parse hexadecimal digits before decimal point
        while let Some(&c) = chars.peek() {
            if c.is_ascii_hexdigit() {
                let digit = c.to_digit(16).unwrap() as f64;
                result = result * 16.0 + digit;
                chars.next();
            } else if c == '.' && !seen_dot {
                seen_dot = true;
                chars.next();
                break;
            } else if c == 'p' || c == 'P' {
                break;
            } else {
                return Err(ParseError::SyntaxError {
                    message: format!("Invalid character '{}' in hexadecimal float literal", c),
                    location,
                });
            }
        }

        // Parse hexadecimal digits after decimal point
        if seen_dot {
            while let Some(&c) = chars.peek() {
                if c.is_ascii_hexdigit() {
                    let digit = c.to_digit(16).unwrap() as f64;
                    result = result * 16.0 + digit;
                    fraction_digits += 1;
                    chars.next();
                } else if c == 'p' || c == 'P' {
                    break;
                } else {
                    return Err(ParseError::SyntaxError {
                        message: format!("Invalid character '{}' in hexadecimal float literal", c),
                        location,
                    });
                }
            }
        }

        // Parse binary exponent
        if let Some(&c) = chars.peek()
            && (c == 'p' || c == 'P')
        {
            chars.next(); // consume 'p' or 'P'

            // Parse optional sign
            let mut exp_negative = false;
            if let Some(&sign) = chars.peek() {
                if sign == '+' {
                    chars.next();
                } else if sign == '-' {
                    exp_negative = true;
                    chars.next();
                }
            }

            // Parse exponent digits
            let mut exp_str = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_ascii_digit() {
                    exp_str.push(c);
                    chars.next();
                } else {
                    break;
                }
            }

            if exp_str.is_empty() {
                return Err(ParseError::SyntaxError {
                    message: "Missing exponent digits in hexadecimal float literal".to_string(),
                    location,
                });
            }

            exponent = exp_str.parse().map_err(|_| ParseError::SyntaxError {
                message: format!(
                    "Invalid exponent '{}' in hexadecimal float literal",
                    exp_str
                ),
                location,
            })?;

            if exp_negative {
                exponent = -exponent;
            }
        }

        // Apply fractional adjustment
        if fraction_digits > 0 {
            result /= 16.0f64.powi(fraction_digits);
        }

        // Apply binary exponent
        if exponent != 0 {
            result *= 2.0f64.powi(exponent);
        }

        // Handle suffix (f, F, l, L) - for now we ignore and return double
        // In a full implementation, we'd return different types based on suffix

        Ok(result)
    }

    /// Main expression parsing using Pratt algorithm
    pub fn parse_expression(
        &mut self,
        min_binding_power: BindingPower,
    ) -> Result<ParseExprOutput, ParseError> {
        trace!(
            "parse_expression: min_binding_power={}",
            min_binding_power.0
        );
        let mut left = self.parse_prefix()?;

        while let Some(current_token) = self.try_current_token() {
            debug!(
                "parse_expression: loop iteration, current token {:?}, min_binding_power={}",
                current_token.kind, min_binding_power.0
            );

            let Some((binding_power, associativity)) =
                PrattParser::get_binding_power(current_token.kind)
            else {
                debug!(
                    "parse_expression: no binding power for {:?}, breaking",
                    current_token.kind
                );
                break;
            };

            if binding_power < min_binding_power {
                debug!(
                    "parse_expression: binding power {:?} < min {:?}, breaking",
                    binding_power.0, min_binding_power.0
                );
                break;
            }

            // Handle associativity
            let next_min_bp = if associativity == Associativity::Right {
                BindingPower(binding_power.0 + 1)
            } else {
                binding_power
            };

            // Parse the right-hand side
            let op_token = self.advance().ok_or_else(|| ParseError::SyntaxError {
                message: "Expected operator".to_string(),
                location: SourceSpan::empty(),
            })?;
            trace!(
                "parse_expression: parsing infix operator {:?}",
                op_token.kind
            );
            let right = self.parse_infix(left, op_token, next_min_bp)?;
            left = right;
        }

        Ok(ParseExprOutput::Expression(left))
    }

    /// Parse prefix expression
    fn parse_prefix(&mut self) -> Result<NodeRef, ParseError> {
        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?;

        debug!("parse_prefix: token={:?} at {}", token.kind, token.location);
        match token.kind {
            TokenKind::Identifier(symbol) => {
                self.advance();
                debug!("parse_prefix: parsed identifier {:?}", symbol);
                let node = self.ast.push_node(Node::new(
                    NodeKind::Ident(symbol, Cell::new(None)),
                    token.location,
                ));
                Ok(node)
            }
            TokenKind::IntegerConstant(value) => {
                self.advance();
                let node = self
                    .ast
                    .push_node(Node::new(NodeKind::LiteralInt(value), token.location));
                Ok(node)
            }
            TokenKind::FloatConstant(text) => {
                self.advance();
                let value = self.parse_c11_float_literal(text)?;
                let node = self.ast.push_node(Node {
                    kind: NodeKind::LiteralFloat(value),
                    span: token.location,
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(node)
            }
            TokenKind::StringLiteral(symbol) => {
                self.advance();
                let node = self.ast.push_node(Node {
                    kind: NodeKind::LiteralString(symbol),
                    span: token.location,
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(node)
            }
            TokenKind::CharacterConstant(codepoint) => {
                self.advance();
                let node = self.ast.push_node(Node {
                    kind: NodeKind::LiteralChar(codepoint as u8 as char),
                    span: token.location,
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(node)
            }
            TokenKind::LeftParen => {
                let left_paren_token = token; // Save the opening paren token for span calculation
                self.advance();
                // Check if this is a cast expression or compound literal by looking ahead for a type name
                if self.is_cast_expression_start() {
                    // Parse the type name
                    let type_ref = self.parse_type_name()?;
                    // Expect closing parenthesis
                    self.expect(TokenKind::RightParen)?;

                    // Check if this is a compound literal (next token is '{')
                    if self.matches(&[TokenKind::LeftBrace]) {
                        // This is a compound literal: (type-name){initializer}
                        return self.parse_compound_literal_from_type_and_start(type_ref, left_paren_token.location.start);
                    } else {
                        // This is a cast expression: (type-name)expression
                        let dummy_right_paren = Token {
                            kind: TokenKind::RightParen,
                            location: SourceSpan::new(left_paren_token.location.end, left_paren_token.location.end),
                        };
                        return self.parse_cast_expression_from_type_and_paren(type_ref, dummy_right_paren);
                    }
                } else {
                    // Regular parenthesized expression
                    let expr = self.parse_expression(BindingPower::MIN)?;
                    self.expect(TokenKind::RightParen)?;
                    match expr {
                        ParseExprOutput::Expression(node) => Ok(node),
                        _ => Err(ParseError::SyntaxError {
                            message: "Expected expression in parentheses".to_string(),
                            location: left_paren_token.location,
                        }),
                    }
                }
            }
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Not
            | TokenKind::Tilde
            | TokenKind::Increment
            | TokenKind::Decrement
            | TokenKind::Star
            | TokenKind::And => self.parse_unary_operator(token),
            TokenKind::Generic => self.parse_generic_selection(),
            TokenKind::Alignof => self.parse_alignof(),
            TokenKind::Sizeof => {
                debug!(
                    "parse_prefix: parsing sizeof expression at position {}",
                    self.current_idx
                );
                self.parse_sizeof()
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: vec![
                    TokenKind::Identifier(Symbol::new("")),
                    TokenKind::IntegerConstant(0),
                    TokenKind::FloatConstant(Symbol::new("0.0")),
                    TokenKind::StringLiteral(Symbol::new("")),
                    TokenKind::CharacterConstant(0),
                    TokenKind::LeftParen,
                ],
                found: token.kind,
                location: token.location,
            }),
        }
    }

    /// Parse unary operator
    fn parse_unary_operator(&mut self, token: Token) -> Result<NodeRef, ParseError> {
        let op = match token.kind {
            TokenKind::Plus => UnaryOp::Plus,
            TokenKind::Minus => UnaryOp::Minus,
            TokenKind::Not => UnaryOp::LogicNot,
            TokenKind::Tilde => UnaryOp::BitNot,
            TokenKind::Increment => UnaryOp::PreIncrement,
            TokenKind::Decrement => UnaryOp::PreDecrement,
            TokenKind::Star => UnaryOp::Deref,
            TokenKind::And => UnaryOp::AddrOf,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Invalid unary operator".to_string(),
                    location: token.location,
                });
            }
        };

        self.advance();
        let operand = self.parse_expression(BindingPower::UNARY)?;
        let operand_node = match operand {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression after unary operator".to_string(),
                    location: token.location,
                });
            }
        };

        let span = SourceSpan::new(
            token.location.start,
            self.ast.get_node(operand_node).span.end,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::UnaryOp(op, operand_node),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse infix operator
    fn parse_infix(
        &mut self,
        left: NodeRef,
        operator_token: Token,
        min_bp: BindingPower,
    ) -> Result<NodeRef, ParseError> {
        debug!(
            "parse_infix: processing operator {:?} at {}",
            operator_token.kind, operator_token.location
        );

        // Handle postfix operators (no right operand) - these should NOT recursively parse expressions
        match operator_token.kind {
            TokenKind::Increment => return self.parse_postfix_increment(left, operator_token),
            TokenKind::Decrement => return self.parse_postfix_decrement(left, operator_token),
            // These operators call special parsing functions that handle their own parsing
            TokenKind::LeftParen => return self.parse_function_call(left),
            TokenKind::LeftBracket => return self.parse_index_access(left),
            TokenKind::Dot => return self.parse_member_access(left, false),
            TokenKind::Arrow => return self.parse_member_access(left, true),
            _ => {}
        }

        // For all other operators, parse the right operand
        let right = self.parse_expression(min_bp)?;
        let right_node = match right {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression after operator".to_string(),
                    location: operator_token.location,
                });
            }
        };

        let op = match operator_token.kind {
            TokenKind::Plus => BinaryOp::Add,
            TokenKind::Minus => BinaryOp::Sub,
            TokenKind::Star => BinaryOp::Mul,
            TokenKind::Slash => BinaryOp::Div,
            TokenKind::Percent => BinaryOp::Mod,
            TokenKind::Equal => BinaryOp::Equal,
            TokenKind::NotEqual => BinaryOp::NotEqual,
            TokenKind::Less => BinaryOp::Less,
            TokenKind::Greater => BinaryOp::Greater,
            TokenKind::LessEqual => BinaryOp::LessEqual,
            TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
            TokenKind::And => BinaryOp::BitAnd,
            TokenKind::Or => BinaryOp::BitOr,
            TokenKind::Xor => BinaryOp::BitXor,
            TokenKind::LeftShift => BinaryOp::LShift,
            TokenKind::RightShift => BinaryOp::RShift,
            TokenKind::LogicAnd => BinaryOp::LogicAnd,
            TokenKind::LogicOr => BinaryOp::LogicOr,
            TokenKind::Assign => BinaryOp::Assign,
            TokenKind::PlusAssign => BinaryOp::AssignAdd,
            TokenKind::MinusAssign => BinaryOp::AssignSub,
            TokenKind::StarAssign => BinaryOp::AssignMul,
            TokenKind::DivAssign => BinaryOp::AssignDiv,
            TokenKind::ModAssign => BinaryOp::AssignMod,
            TokenKind::AndAssign => BinaryOp::AssignBitAnd,
            TokenKind::OrAssign => BinaryOp::AssignBitOr,
            TokenKind::XorAssign => BinaryOp::AssignBitXor,
            TokenKind::LeftShiftAssign => BinaryOp::AssignLShift,
            TokenKind::RightShiftAssign => BinaryOp::AssignRShift,
            TokenKind::Comma => BinaryOp::Comma,
            TokenKind::Question => return self.parse_ternary(left, right_node),
            TokenKind::LeftParen => return self.parse_function_call(left),
            TokenKind::LeftBracket => return self.parse_index_access(left),
            TokenKind::Dot => return self.parse_member_access(left, false),
            TokenKind::Arrow => return self.parse_member_access(left, true),
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Invalid binary operator".to_string(),
                    location: operator_token.location,
                });
            }
        };

        let span = SourceSpan::new(
            self.ast.get_node(left).span.start,
            self.ast.get_node(right_node).span.end,
        );

        let node = self
            .ast
            .push_node(Node::new(NodeKind::BinaryOp(op, left, right_node), span));
        Ok(node)
    }

    /// Parse ternary operator
    fn parse_ternary(
        &mut self,
        condition: NodeRef,
        true_expr: NodeRef,
    ) -> Result<NodeRef, ParseError> {
        self.expect(TokenKind::Colon)?;
        let false_expr_result = self.parse_expression(BindingPower::CONDITIONAL)?;
        let false_expr = match false_expr_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in ternary false branch".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        let span = SourceSpan::new(
            self.ast.get_node(condition).span.start,
            self.ast.get_node(false_expr).span.end,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::TernaryOp(condition, true_expr, false_expr),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse function call
    fn parse_function_call(&mut self, function: NodeRef) -> Result<NodeRef, ParseError> {
        debug!("parse_function_call: parsing function call with LeftParen");
        let mut args = Vec::new();

        // Handle empty argument list: foo()
        if self.accept(TokenKind::RightParen).is_some() {
            debug!("parse_function_call: empty argument list");
            // Empty argument list - RightParen already consumed, no need to expect it again
            debug!(
                "parse_function_call: successfully parsed function call with {} arguments",
                args.len()
            );
        } else {
            debug!("parse_function_call: parsing arguments");
            loop {
                let arg_result = self.parse_expression(BindingPower::MIN)?;
                let arg = match arg_result {
                    ParseExprOutput::Expression(node) => node,
                    _ => {
                        return Err(ParseError::SyntaxError {
                            message: "Expected expression in function call argument".to_string(),
                            location: self.current_token().unwrap().location,
                        });
                    }
                };
                args.push(arg);
                debug!(
                    "parse_function_call: parsed argument, count: {}",
                    args.len()
                );

                if self.accept(TokenKind::Comma).is_some() {
                    debug!("parse_function_call: found comma, continuing to next argument");
                    // Continue to next argument - the loop will parse it
                } else {
                    debug!("parse_function_call: no comma found, expecting RightParen");
                    break;
                }
            }

            let right_paren_token = self.expect(TokenKind::RightParen)?;
            debug!(
                "parse_function_call: successfully parsed function call with {} arguments",
                args.len()
            );

            let span = SourceSpan::new(
                self.ast.get_node(function).span.start,
                right_paren_token.location.end,
            );

            let node = self.ast.push_node(Node {
                kind: NodeKind::FunctionCall(function, args),
                span,
                resolved_type: Cell::new(None),
                resolved_symbol: Cell::new(None),
            });
            return Ok(node);
        }

        // Handle the empty argument case - create the node here
        let span = SourceSpan::new(
            self.ast.get_node(function).span.start,
            // Use the current token location since we don't have the right paren token
            self.current_token_span()?.start,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::FunctionCall(function, args),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse array index access
    fn parse_index_access(&mut self, array: NodeRef) -> Result<NodeRef, ParseError> {
        debug!(
            "parse_index_access: parsing array index, current token {:?}",
            self.current_token_kind()
        );

        // The LeftBracket was already consumed by parse_infix.
        // Since the expression parsing loop stopped at the RightBracket,
        // we need to handle the case where RightBracket is the current token.
        // This means we have an empty index [].

        let index_node = if self.matches(&[TokenKind::RightBracket]) {
            debug!("parse_index_access: empty array index []");
            // Create a placeholder for empty index
            self.ast.push_node(Node {
                kind: NodeKind::LiteralInt(0), // Use 0 as placeholder
                span: self.current_token().unwrap().location,
                resolved_type: Cell::new(None),
                resolved_symbol: Cell::new(None),
            })
        } else {
            // This should not happen in normal array access, but handle it just in case
            debug!(
                "parse_index_access: unexpected token in array access, trying to parse expression"
            );
            let index_result = self.parse_expression(BindingPower::MIN)?;
            match index_result {
                ParseExprOutput::Expression(node) => {
                    debug!("parse_index_access: parsed index expression");
                    node
                }
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in array index".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        // The RightBracket should now be the current token, consume it
        debug!(
            "parse_index_access: expecting RightBracket, current token is {:?}",
            self.current_token_kind()
        );
        let right_bracket_token = self.expect(TokenKind::RightBracket)?;
        debug!(
            "parse_index_access: parsed closing bracket, current token now {:?}",
            self.current_token_kind()
        );

        let span = SourceSpan::new(
            self.ast.get_node(array).span.start,
            right_bracket_token.location.end,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::IndexAccess(array, index_node),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse member access
    fn parse_member_access(
        &mut self,
        object: NodeRef,
        is_arrow: bool,
    ) -> Result<NodeRef, ParseError> {
        let member_token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected member name".to_string(),
                location: SourceSpan::empty(),
            })?;

        let member_symbol = match member_token.kind {
            TokenKind::Identifier(symbol) => symbol,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![TokenKind::Identifier(Symbol::new(""))],
                    found: member_token.kind,
                    location: member_token.location,
                });
            }
        };

        self.advance();

        let span = SourceSpan::new(
            self.ast.get_node(object).span.start,
            member_token.location.end,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::MemberAccess(object, member_symbol, is_arrow),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse postfix increment
    fn parse_postfix_increment(
        &mut self,
        operand: NodeRef,
        operator_token: Token,
    ) -> Result<NodeRef, ParseError> {
        let span = SourceSpan::new(
            self.ast.get_node(operand).span.start,
            operator_token.location.end,
        );

        let node = self
            .ast
            .push_node(Node::new(NodeKind::PostIncrement(operand), span));
        Ok(node)
    }

    /// Parse postfix decrement
    fn parse_postfix_decrement(
        &mut self,
        operand: NodeRef,
        operator_token: Token,
    ) -> Result<NodeRef, ParseError> {
        let span = SourceSpan::new(
            self.ast.get_node(operand).span.start,
            operator_token.location.end,
        );

        let node = self
            .ast
            .push_node(Node::new(NodeKind::PostDecrement(operand), span));
        Ok(node)
    }

    /// Parse a declaration
    pub fn parse_declaration(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        let initial_idx = self.current_idx; // Save initial position for potential rollback
        let saved_diagnostic_count = self.diag.diagnostics.len();

        debug!(
            "parse_declaration: starting at position {}, token {:?}",
            initial_idx,
            self.current_token_kind()
        );

        // Check for _Static_assert (C11)
        if let Some(token) = self.accept(TokenKind::StaticAssert) {
            return self.parse_static_assert(token);
        }

        // Try to parse declaration specifiers
        let specifiers = match self.parse_declaration_specifiers() {
            Ok(specifiers) => {
                debug!(
                    "parse_declaration: parsed {} specifiers, current token {:?}",
                    specifiers.len(),
                    self.current_token_kind()
                );
                debug!(
                    "parse_declaration: current token after specifiers: {:?}",
                    self.current_token_kind()
                );
                if let Some(last_specifier) = specifiers.last() {
                    debug!(
                        "parse_declaration: last specifier type: {:?}",
                        std::mem::discriminant(&last_specifier.type_specifier)
                    );
                }
                specifiers
            }
            Err(e) => {
                // If declaration specifiers parsing fails, roll back completely
                self.current_idx = initial_idx;
                self.diag.diagnostics.truncate(saved_diagnostic_count);
                debug!(
                    "parse_declaration: specifier parsing failed, rolled back to {}",
                    initial_idx
                );
                return Err(e);
            }
        };

        // Special handling for struct/union/enum declarations
        // Check if any specifier is a struct/union/enum specifier (definition or forward declaration)
        let is_record_enum_specifier = specifiers.iter().any(|s| matches!(&s.type_specifier, TypeSpecifier::Record(_, _, _) | TypeSpecifier::Enum(_, _)) && s.storage_class.is_none());

        // If we have a struct/union/enum specifier, we need to check if there are declarators following
        // The logic should be:
        // - If next token is semicolon: treat as record/enum declaration (definition or forward)
        // - If next token is declarator-starting token: continue with normal declaration parsing
        if is_record_enum_specifier {
            if self.matches(&[TokenKind::Semicolon]) {
                // This is either:
                // 1. A pure struct/union/enum definition like "struct foo { ... };" or "enum E { ... };"
                // 2. A forward struct/union/enum declaration like "struct foo;" or "enum E;"
                // In both cases, consume the semicolon and create declaration with no declarators
                self.expect(TokenKind::Semicolon)?;

                let declaration_data = DeclarationData {
                    specifiers,
                    init_declarators: Vec::new(),
                };

                let end_span = self.current_token()?.location.end;
                let span = SourceSpan::new(start_span, end_span);

                let node = self
                    .ast
                    .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
                debug!(
                    "parse_declaration: successfully parsed record/enum declaration, node_id={}",
                    node.get()
                );
                return Ok(node);
            } else {
                // This is a record/enum specifier with declarators
                // Continue with normal declaration parsing (e.g., "struct foo { ... } var;")
                debug!(
                    "parse_declaration: record/enum specifier with declarators, continuing with normal parsing"
                );
            }
        }

        // For all other cases, check if we have declarators
        let has_declarators = if self.matches(&[TokenKind::Semicolon]) {
            // Definitely no declarators
            false
        } else {
            // Check if we have a declarator-starting token
            // This includes: identifier, star, or left paren
            matches!(
                self.current_token_kind(),
                Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
            )
        };
        debug!("parse_declaration: has_declarators = {}", has_declarators);

        // If no declarators and this is not a record/enum definition, it's an error
        if !has_declarators {
            // Check if this looks like a record/enum definition
            // by looking at the last parsed specifier
            if let Some(last_specifier) = specifiers.last() {
                match &last_specifier.type_specifier {
                    TypeSpecifier::Record(_, _tag, _definition) => {
                        // This should not happen due to the check above, but just in case
                        self.current_idx = initial_idx;
                        self.diag.diagnostics.truncate(saved_diagnostic_count);
                        debug!(
                            "parse_declaration: record definition with no declarators and no semicolon, rolled back to {}",
                            initial_idx
                        );
                        return Err(ParseError::SyntaxError {
                            message: "Expected ';' after struct/union definition".to_string(),
                            location: self.current_token()?.location,
                        });
                    }
                    TypeSpecifier::Enum(_tag, _definition) => {
                        // This should not happen due to the check above, but just in case
                        self.current_idx = initial_idx;
                        self.diag.diagnostics.truncate(saved_diagnostic_count);
                        debug!(
                            "parse_declaration: enum definition with no declarators and no semicolon, rolled back to {}",
                            initial_idx
                        );
                        return Err(ParseError::SyntaxError {
                            message: "Expected ';' after enum definition".to_string(),
                            location: self.current_token()?.location,
                        });
                    }
                    _ => {
                        // Not a record/enum definition, this is likely an error
                        // But let's rollback and let the statement parser handle it
                        self.current_idx = initial_idx;
                        self.diag.diagnostics.truncate(saved_diagnostic_count);
                        debug!(
                            "parse_declaration: no declarators found, rolled back to {}",
                            initial_idx
                        );
                        return Err(ParseError::SyntaxError {
                            message: "Expected declarator or identifier after type specifier"
                                .to_string(),
                            location: self.current_token()?.location,
                        });
                    }
                }
            } else {
                // No specifiers at all - this shouldn't happen
                self.current_idx = initial_idx;
                self.diag.diagnostics.truncate(saved_diagnostic_count);
                debug!(
                    "parse_declaration: no specifiers, rolled back to {}",
                    initial_idx
                );
                return Err(ParseError::SyntaxError {
                    message: "Expected type specifiers".to_string(),
                    location: self.current_token()?.location,
                });
            }
        }

        // Parse init declarators
        let mut init_declarators = Vec::new();

        loop {
            let declarator_start_idx = self.current_idx;
            debug!(
                "parse_declaration: parsing declarator at position {}, token {:?}",
                declarator_start_idx,
                self.current_token_kind()
            );

            let declarator = match self.parse_declarator(None) {
                Ok(declarator) => {
                    debug!(
                        "parse_declaration: parsed declarator, current token {:?}",
                        self.current_token_kind()
                    );
                    declarator
                }
                Err(e) => {
                    // If declarator parsing fails, roll back completely
                    self.current_idx = initial_idx;
                    self.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: declarator parsing failed, rolled back to {}",
                        initial_idx
                    );
                    return Err(e);
                }
            };

            let _initializer_start_idx = self.current_idx;
            let initializer = if self.matches(&[TokenKind::Assign]) {
                self.advance(); // consume '='
                debug!(
                    "parse_declaration: found '=', parsing initializer at position {}",
                    self.current_idx
                );
                match self.parse_initializer() {
                    Ok(initializer) => {
                        debug!(
                            "parse_declaration: parsed initializer, now at position {} with token {:?}",
                            self.current_idx,
                            self.current_token_kind()
                        );
                        Some(initializer)
                    }
                    Err(e) => {
                        // If initializer parsing fails, roll back completely
                        self.current_idx = initial_idx;
                        self.diag.diagnostics.truncate(saved_diagnostic_count);
                        debug!(
                            "parse_declaration: initializer parsing failed, rolled back to {}",
                            initial_idx
                        );
                        return Err(e);
                    }
                }
            } else {
                None
            };

            init_declarators.push(InitDeclarator {
                declarator,
                initializer,
            });

            if !self.matches(&[TokenKind::Comma]) {
                break;
            }
            self.advance(); // consume comma
        }

        // Check for semicolon at current position
        debug!(
            "parse_declaration: expecting semicolon, current token {:?}",
            self.current_token_kind()
        );
        let semicolon_token = if self.matches(&[TokenKind::Semicolon]) {
            self.advance().ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?
        } else {
            // If semicolon is missing, roll back completely
            self.current_idx = initial_idx;
            self.diag.diagnostics.truncate(saved_diagnostic_count);
            debug!(
                "parse_declaration: missing semicolon, rolled back to {}",
                initial_idx
            );
            return Err(ParseError::SyntaxError {
                message: "Expected ';' after declaration".to_string(),
                location: self.current_token()?.location,
            });
        };

        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        // Track typedef names for disambiguation
        for specifier in &specifiers {
            if specifier.storage_class == Some(StorageClass::Typedef) {
                for init_declarator in &init_declarators {
                    if let Some(name) = self.get_declarator_name(&init_declarator.declarator) {
                        self.typedef_names.insert(name);
                    }
                }
            }
        }

        let declaration_data = DeclarationData {
            specifiers,
            init_declarators,
        };

        let node = self
            .ast
            .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
        debug!(
            "parse_declaration: successfully parsed declaration, node_id={}",
            node.get()
        );
        Ok(node)
    }

    /// Parse declaration specifiers
    fn parse_declaration_specifiers(&mut self) -> Result<Vec<DeclSpecifier>, ParseError> {
        let mut specifiers = Vec::new();
        let mut has_type_specifier = false;
        let start_idx = self.current_idx;

        debug!(
            "parse_declaration_specifiers: starting at position {}, token {:?}",
            start_idx,
            self.current_token_kind()
        );

        while let Some(token) = self.try_current_token() {
            debug!(
                "parse_declaration_specifiers: loop iteration at position {}, token {:?}",
                self.current_idx, token.kind
            );
            match token.kind {
                // Storage class specifiers
                TokenKind::Typedef
                | TokenKind::Extern
                | TokenKind::Static
                | TokenKind::Auto
                | TokenKind::Register
                | TokenKind::ThreadLocal => {
                    let storage_class = match token.kind {
                        TokenKind::Typedef => StorageClass::Typedef,
                        TokenKind::Extern => StorageClass::Extern,
                        TokenKind::Static => StorageClass::Static,
                        TokenKind::Auto => StorageClass::Auto,
                        TokenKind::Register => StorageClass::Register,
                        TokenKind::ThreadLocal => StorageClass::ThreadLocal,
                        _ => unreachable!(),
                    };
                    self.advance();
                    specifiers.push(DeclSpecifier {
                        storage_class: Some(storage_class),
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier: TypeSpecifier::Void, // Placeholder
                    });
                }

                // Type qualifiers
                TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic => {
                    let mut qualifiers = TypeQualifiers::empty();
                    while let Some(token) = self.try_current_token() {
                        match token.kind {
                            TokenKind::Const => qualifiers.insert(TypeQualifiers::CONST),
                            TokenKind::Volatile => qualifiers.insert(TypeQualifiers::VOLATILE),
                            TokenKind::Restrict => qualifiers.insert(TypeQualifiers::RESTRICT),
                            TokenKind::Atomic => qualifiers.insert(TypeQualifiers::ATOMIC),
                            _ => break,
                        }
                        self.advance();
                    }
                    specifiers.push(DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: qualifiers,
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier: TypeSpecifier::Void, // Placeholder
                    });
                }

                // Function specifiers
                TokenKind::Inline | TokenKind::Noreturn => {
                    let mut func_specs = FunctionSpecifiers::empty();
                    while let Some(token) = self.try_current_token() {
                        match token.kind {
                            TokenKind::Inline => func_specs.insert(FunctionSpecifiers::INLINE),
                            TokenKind::Noreturn => func_specs.insert(FunctionSpecifiers::NORETURN),
                            _ => break,
                        }
                        self.advance();
                    }
                    specifiers.push(DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: func_specs,
                        alignment_specifier: None,
                        type_specifier: TypeSpecifier::Void, // Placeholder
                    });
                }

                // Type specifiers
                TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum => {
                    let type_specifier = self.parse_type_specifier()?;
                    specifiers.push(DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier,
                    });
                    has_type_specifier = true;
                }

                TokenKind::Identifier(symbol) => {
                    debug!(
                        "parse_declaration_specifiers: found identifier {:?}, calling is_type_name, current position: {}",
                        symbol, self.current_idx
                    );
                    if self.is_type_name(symbol) && !has_type_specifier {
                        debug!(
                            "parse_declaration_specifiers: {:?} is a type name and no type specifier yet, parsing type specifier",
                            symbol
                        );
                        let type_specifier = self.parse_type_specifier()?;
                        specifiers.push(DeclSpecifier {
                            storage_class: None,
                            type_qualifiers: TypeQualifiers::empty(),
                            function_specifiers: FunctionSpecifiers::empty(),
                            alignment_specifier: None,
                            type_specifier,
                        });
                        has_type_specifier = true;
                    } else {
                        debug!(
                            "parse_declaration_specifiers: {:?} is not a type name or already have type specifier, breaking at position {}",
                            symbol, self.current_idx
                        );
                        break;
                    }
                }

                // Alignment specifier
                TokenKind::Alignas => {
                    self.advance(); // consume _Alignas
                    let alignment = if self.matches(&[TokenKind::LeftParen]) {
                        self.advance(); // consume '('
                        if self.matches(&[TokenKind::Identifier(Symbol::new(""))]) {
                            // _Alignas(type-name)
                            let type_ref = self.parse_type_name()?;
                            self.expect(TokenKind::RightParen)?;
                            AlignmentSpecifier::Type(type_ref)
                        } else {
                            // _Alignas(constant-expression)
                            let expr_result = self.parse_expression(BindingPower::MIN)?;
                            let expr = match expr_result {
                                ParseExprOutput::Expression(node) => node,
                                _ => {
                                    return Err(ParseError::SyntaxError {
                                        message: "Expected expression in _Alignas".to_string(),
                                        location: self.current_token().unwrap().location,
                                    });
                                }
                            };
                            self.expect(TokenKind::RightParen)?;
                            AlignmentSpecifier::Expr(expr)
                        }
                    } else {
                        return Err(ParseError::SyntaxError {
                            message: "Expected '(' after _Alignas".to_string(),
                            location: token.location,
                        });
                    };

                    specifiers.push(DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: Some(alignment),
                        type_specifier: TypeSpecifier::Void, // Placeholder
                    });
                }

                _ => {
                    debug!(
                        "parse_declaration_specifiers: token {:?} not recognized as declaration specifier, breaking",
                        token.kind
                    );
                    break;
                }
            }
        }

        debug!(
            "parse_declaration_specifiers: ending at position {}, specifiers len={}, found {} specifiers",
            self.current_idx,
            specifiers.len(),
            specifiers.len()
        );

        if specifiers.is_empty() {
            return Err(ParseError::SyntaxError {
                message: "Expected declaration specifiers".to_string(),
                location: self.current_token().unwrap().location,
            });
        }

        Ok(specifiers)
    }

    /// Parse type specifier
    fn parse_type_specifier(&mut self) -> Result<TypeSpecifier, ParseError> {
        self.parse_type_specifier_with_context(false)
    }

    /// Parse type specifier with context
    fn parse_type_specifier_with_context(
        &mut self,
        in_struct_member: bool,
    ) -> Result<TypeSpecifier, ParseError> {
        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected type specifier".to_string(),
                location: SourceSpan::empty(),
            })?;

        match token.kind {
            TokenKind::Void => {
                self.advance();
                Ok(TypeSpecifier::Void)
            }
            TokenKind::Char => {
                self.advance();
                Ok(TypeSpecifier::Char)
            }
            TokenKind::Short => {
                self.advance();
                Ok(TypeSpecifier::Short)
            }
            TokenKind::Int => {
                self.advance();
                Ok(TypeSpecifier::Int)
            }
            TokenKind::Long => {
                self.advance();
                // Check for long long or long double
                if let Some(next_token) = self.try_current_token() {
                    match next_token.kind {
                        TokenKind::Long => {
                            self.advance();
                            Ok(TypeSpecifier::LongLong)
                        }
                        TokenKind::Double => {
                            self.advance();
                            Ok(TypeSpecifier::LongDouble)
                        }
                        _ => Ok(TypeSpecifier::Long),
                    }
                } else {
                    Ok(TypeSpecifier::Long)
                }
            }
            TokenKind::Float => {
                self.advance();
                Ok(TypeSpecifier::Float)
            }
            TokenKind::Double => {
                self.advance();
                Ok(TypeSpecifier::Double)
            }
            TokenKind::Signed => {
                self.advance();
                Ok(TypeSpecifier::Signed)
            }
            TokenKind::Unsigned => {
                self.advance();
                Ok(TypeSpecifier::Unsigned)
            }
            TokenKind::Bool => {
                self.advance();
                Ok(TypeSpecifier::Bool)
            }
            TokenKind::Complex => {
                self.advance();
                // Parse optional base type for _Complex (C11 allows _Complex float, _Complex double, etc.)
                if self.matches(&[TokenKind::Float, TokenKind::Double, TokenKind::Long]) {
                    // For now, just consume the base type - full implementation would create proper type
                    self.advance();
                    if self.matches(&[TokenKind::Double]) {
                        self.advance(); // consume double for long double
                    }
                }
                Ok(TypeSpecifier::Complex)
            }
            TokenKind::Atomic => {
                self.advance();
                self.expect(TokenKind::LeftParen)?;
                let type_ref = self.parse_type_name()?;
                self.expect(TokenKind::RightParen)?;
                Ok(TypeSpecifier::Atomic(type_ref))
            }
            TokenKind::Struct => {
                self.advance();
                self.parse_record_specifier_with_context(false, in_struct_member)
            }
            TokenKind::Union => {
                self.advance();
                self.parse_record_specifier_with_context(true, in_struct_member)
            }
            TokenKind::Enum => {
                self.advance();
                self.parse_enum_specifier()
            }
            TokenKind::Identifier(symbol) => {
                self.advance();
                Ok(TypeSpecifier::TypedefName(symbol))
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: vec![
                    TokenKind::Void,
                    TokenKind::Char,
                    TokenKind::Short,
                    TokenKind::Int,
                    TokenKind::Long,
                    TokenKind::Float,
                    TokenKind::Double,
                    TokenKind::Signed,
                    TokenKind::Unsigned,
                    TokenKind::Bool,
                    TokenKind::Complex,
                    TokenKind::Atomic,
                    TokenKind::Struct,
                    TokenKind::Union,
                    TokenKind::Enum,
                    TokenKind::Identifier(Symbol::new("")),
                ],
                found: token.kind,
                location: token.location,
            }),
        }
    }

    /// Parse struct or union specifier with context
    fn parse_record_specifier_with_context(
        &mut self,
        is_union: bool,
        in_struct_member: bool,
    ) -> Result<TypeSpecifier, ParseError> {
        let tag = if let Some(token) = self.try_current_token() {
            if let TokenKind::Identifier(symbol) = token.kind {
                self.advance();
                Some(symbol)
            } else {
                None
            }
        } else {
            None
        };

        // In struct member context, only parse members if we have a specific tag
        // to avoid confusion with anonymous nested structs
        let definition =
            if self.matches(&[TokenKind::LeftBrace]) && (!in_struct_member || tag.is_some()) {
                self.advance(); // consume '{'
                let members = self.parse_struct_declaration_list()?;
                self.expect(TokenKind::RightBrace)?;
                Some(RecordDefData {
                    tag,
                    members: Some(members),
                    is_union,
                })
            } else {
                None
            };

        Ok(TypeSpecifier::Record(is_union, tag, definition))
    }

    /// Parse enum specifier
    fn parse_enum_specifier(&mut self) -> Result<TypeSpecifier, ParseError> {
        let tag = if let Some(token) = self.try_current_token() {
            if let TokenKind::Identifier(symbol) = token.kind {
                self.advance().ok_or_else(|| ParseError::SyntaxError {
                    message: "Unexpected end of input".to_string(),
                    location: SourceSpan::empty(),
                })?;
                Some(symbol)
            } else {
                None
            }
        } else {
            None
        };

        let enumerators = if self.matches(&[TokenKind::LeftBrace]) {
            self.advance(); // consume '{'
            let enums = self.parse_enumerator_list()?;
            self.expect(TokenKind::RightBrace)?;
            Some(enums)
        } else {
            None
        };

        Ok(TypeSpecifier::Enum(tag, enumerators))
    }

    /// Parse struct declaration list
    fn parse_struct_declaration_list(&mut self) -> Result<Vec<DeclarationData>, ParseError> {
        let mut declarations = Vec::new();

        while !self.matches(&[TokenKind::RightBrace]) {
            let declaration = self.parse_struct_declaration()?;
            declarations.push(declaration);
        }

        Ok(declarations)
    }

    /// Parse struct declaration
    fn parse_struct_declaration(&mut self) -> Result<DeclarationData, ParseError> {
        // Check if we have an anonymous struct/union
        if self.matches(&[TokenKind::Struct, TokenKind::Union]) {
            let is_union = self.matches(&[TokenKind::Union]);
            self.advance(); // consume struct/union

            // Check if this is an anonymous struct
            if self.matches(&[TokenKind::LeftBrace]) {
                // Anonymous struct definition
                self.expect(TokenKind::LeftBrace)?;
                let members = self.parse_struct_declaration_list()?;
                self.expect(TokenKind::RightBrace)?;

                // After parsing { members }, check the next token
                // If the next token is ';', treat it as an anonymous struct member (no declarator needed)
                // If the next token is an identifier or declarator start, continue with variable declaration parsing
                let init_declarators = if self.matches(&[TokenKind::Semicolon]) {
                    // Anonymous struct member: struct { members };
                    self.expect(TokenKind::Semicolon)?;
                    Vec::new()
                } else {
                    // Variable declaration with anonymous struct type: struct { members } variable;
                    vec![InitDeclarator {
                        declarator: self.parse_declarator(None)?,
                        initializer: None,
                    }]
                };

                let type_specifier = TypeSpecifier::Record(
                    is_union,
                    None,
                    Some(RecordDefData {
                        tag: None,
                        members: Some(members),
                        is_union,
                    }),
                );

                let specifiers = vec![DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier,
                }];

                // Only expect semicolon if we haven't already consumed it in the anonymous case
                if !init_declarators.is_empty() {
                    self.expect(TokenKind::Semicolon)?;
                }

                return Ok(DeclarationData {
                    specifiers,
                    init_declarators,
                });
            } else {
                // Named struct - read the tag first
                let tag = if let Some(token) = self.try_current_token() {
                    if let TokenKind::Identifier(symbol) = token.kind {
                        self.advance();
                        Some(symbol)
                    } else {
                        None
                    }
                } else {
                    None
                };

                // Check if it's defined inline
                if self.matches(&[TokenKind::LeftBrace]) {
                    // Named struct with definition
                    self.expect(TokenKind::LeftBrace)?;
                    let members = self.parse_struct_declaration_list()?;
                    self.expect(TokenKind::RightBrace)?;

                    // After parsing { members }, check the next token
                    let init_declarators = if self.matches(&[TokenKind::Semicolon]) {
                        // Named struct definition: struct tag { members };
                        self.expect(TokenKind::Semicolon)?;
                        Vec::new()
                    } else {
                        // Variable declaration with named struct type: struct tag { members } variable;
                        vec![InitDeclarator {
                            declarator: self.parse_declarator(None)?,
                            initializer: None,
                        }]
                    };

                    let type_specifier = TypeSpecifier::Record(
                        is_union,
                        tag,
                        Some(RecordDefData {
                            tag,
                            members: Some(members),
                            is_union,
                        }),
                    );

                    let specifiers = vec![DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier,
                    }];

                    // Only expect semicolon if we haven't already consumed it
                    if !init_declarators.is_empty() {
                        self.expect(TokenKind::Semicolon)?;
                    }

                    return Ok(DeclarationData {
                        specifiers,
                        init_declarators,
                    });
                } else {
                    // Just a forward declaration or reference to named struct
                    let type_specifier = TypeSpecifier::Record(is_union, tag, None);
                    let declarator = self.parse_declarator(None)?;

                    let specifiers = vec![DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier,
                    }];

                    self.expect(TokenKind::Semicolon)?;

                    return Ok(DeclarationData {
                        specifiers,
                        init_declarators: vec![InitDeclarator {
                            declarator,
                            initializer: None,
                        }],
                    });
                }
            }
        } else {
            // Regular member: type specifier + multiple declarators
            let type_specifier = self.parse_type_specifier_with_context(true)?;

            let mut init_declarators = Vec::new();
            loop {
                let declarator = self.parse_declarator(None)?;
                init_declarators.push(InitDeclarator {
                    declarator,
                    initializer: None,
                });

                if !self.matches(&[TokenKind::Comma]) {
                    break;
                }
                self.advance(); // consume comma
            }

            let specifiers = vec![DeclSpecifier {
                storage_class: None,
                type_qualifiers: TypeQualifiers::empty(),
                function_specifiers: FunctionSpecifiers::empty(),
                alignment_specifier: None,
                type_specifier,
            }];

            self.expect(TokenKind::Semicolon)?;

            return Ok(DeclarationData {
                specifiers,
                init_declarators,
            });
        }
    }

    /// Parse enumerator list
    fn parse_enumerator_list(&mut self) -> Result<Vec<NodeRef>, ParseError> {
        let mut enumerators = Vec::new();

        loop {
            let enumerator = self.parse_enumerator()?;
            enumerators.push(enumerator);

            if !self.matches(&[TokenKind::Comma]) {
                break;
            }
            self.advance(); // consume comma

            // Allow trailing comma
            if self.matches(&[TokenKind::RightBrace]) {
                break;
            }
        }

        Ok(enumerators)
    }

    /// Parse enumerator
    fn parse_enumerator(&mut self) -> Result<NodeRef, ParseError> {
        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected enumerator name".to_string(),
                location: SourceSpan::empty(),
            })?;

        let name = match token.kind {
            TokenKind::Identifier(symbol) => symbol,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![TokenKind::Identifier(Symbol::new(""))],
                    found: token.kind,
                    location: token.location,
                });
            }
        };

        self.advance().ok_or_else(|| ParseError::SyntaxError {
            message: "Unexpected end of input".to_string(),
            location: SourceSpan::empty(),
        })?;

        let value = if self.matches(&[TokenKind::Assign]) {
            self.advance(); // consume '='
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression for enumerator value".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        } else {
            None
        };

        let span = SourceSpan::new(token.location.start, token.location.end);

        let node = self.ast.push_node(Node {
            kind: NodeKind::EnumConstant(name, value),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse type name (for casts, sizeof, etc.)
    fn parse_type_name(&mut self) -> Result<TypeRef, ParseError> {
        // Parse declaration specifiers
        let _specifiers = self.parse_declaration_specifiers()?;

        // Parse abstract declarator (optional)
        let _declarator = if self.is_abstract_declarator_start() {
            Some(self.parse_abstract_declarator()?)
        } else {
            None
        };

        // Build the type from specifiers and declarator
        // TODO: Implement proper type construction from specifiers and declarator
        Ok(self.ast.push_type(Type {
            kind: TypeKind::Void,
            qualifiers: TypeQualifiers::empty(),
            size: None,
            alignment: None,
        }))
    }

    /// Parse initializer
    fn parse_initializer(&mut self) -> Result<Initializer, ParseError> {
        debug!(
            "parse_initializer: called at position {}, current token: {:?}",
            self.current_idx,
            self.current_token_kind()
        );
        if self.matches(&[TokenKind::LeftBrace]) {
            debug!("parse_initializer: found LeftBrace, parsing compound initializer");
            // Compound initializer
            self.advance(); // consume '{'
            let mut initializers = Vec::new();

            while !self.matches(&[TokenKind::RightBrace]) {
                // Check if this is a designated initializer (starts with . or [)
                let is_designated =
                    self.matches(&[TokenKind::Dot]) || self.matches(&[TokenKind::LeftBracket]);

                let initializer = if is_designated {
                    // Parse designated initializer
                    let designated_init = self.parse_designated_initializer()?;
                    designated_init
                } else {
                    // Parse regular initializer (expression or nested compound initializer)
                    let expr_or_compound = if self.matches(&[TokenKind::LeftBrace]) {
                        // Nested compound initializer
                        self.parse_initializer()?
                    } else {
                        // Expression initializer
                        let expr_result = self.parse_expression(BindingPower::MIN)?;
                        match expr_result {
                            ParseExprOutput::Expression(node) => Initializer::Expression(node),
                            _ => {
                                return Err(ParseError::SyntaxError {
                                    message: "Expected expression in initializer".to_string(),
                                    location: self.current_token().unwrap().location,
                                });
                            }
                        }
                    };

                    // Wrap in DesignatedInitializer with empty designation
                    DesignatedInitializer {
                        designation: Vec::new(),
                        initializer: expr_or_compound,
                    }
                };

                initializers.push(initializer);

                if !self.matches(&[TokenKind::Comma]) {
                    break;
                }
                self.advance(); // consume comma
            }

            self.expect(TokenKind::RightBrace)?;
            Ok(Initializer::List(initializers))
        } else {
            debug!(
                "parse_initializer: no LeftBrace found, current token: {:?}, trying expression initializer",
                self.current_token_kind()
            );
            // Expression initializer
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Ok(Initializer::Expression(node)),
                _ => Err(ParseError::SyntaxError {
                    message: "Expected expression in initializer".to_string(),
                    location: self.current_token().unwrap().location,
                }),
            }
        }
    }

    /// Parse designated initializer
    fn parse_designated_initializer(&mut self) -> Result<DesignatedInitializer, ParseError> {
        let designation =
            if self.matches(&[TokenKind::Dot]) || self.matches(&[TokenKind::LeftBracket]) {
                self.parse_designation()?
            } else {
                Vec::new()
            };

        self.expect(TokenKind::Assign)?;
        let initializer = self.parse_initializer()?;

        Ok(DesignatedInitializer {
            designation,
            initializer,
        })
    }

    /// Parse designation
    fn parse_designation(&mut self) -> Result<Vec<Designator>, ParseError> {
        let mut designators = Vec::new();

        while self.matches(&[TokenKind::Dot]) || self.matches(&[TokenKind::LeftBracket]) {
            if self.matches(&[TokenKind::Dot]) {
                self.advance(); // consume '.'
                let token = self
                    .try_current_token()
                    .ok_or_else(|| ParseError::SyntaxError {
                        message: "Expected field name".to_string(),
                        location: SourceSpan::empty(),
                    })?;

                let field_name = match token.kind {
                    TokenKind::Identifier(symbol) => symbol,
                    _ => {
                        return Err(ParseError::UnexpectedToken {
                            expected: vec![TokenKind::Identifier(Symbol::new(""))],
                            found: token.kind,
                            location: token.location,
                        });
                    }
                };

                self.advance().ok_or_else(|| ParseError::SyntaxError {
                    message: "Unexpected end of input".to_string(),
                    location: SourceSpan::empty(),
                })?;
                designators.push(Designator::FieldName(field_name));
            } else if self.matches(&[TokenKind::LeftBracket]) {
                self.advance(); // consume '['
                let expr_result = self.parse_expression(BindingPower::MIN)?;
                let index_expr = match expr_result {
                    ParseExprOutput::Expression(node) => node,
                    _ => {
                        return Err(ParseError::SyntaxError {
                            message: "Expected expression in array designator".to_string(),
                            location: self.current_token().unwrap().location,
                        });
                    }
                };
                self.expect(TokenKind::RightBracket)?;
                designators.push(Designator::ArrayIndex(index_expr));
            }
        }

        Ok(designators)
    }

    /// Parse declarator
    fn parse_declarator(
        &mut self,
        initial_declarator: Option<Symbol>,
    ) -> Result<Declarator, ParseError> {
        let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
        let mut _current_qualifiers = TypeQualifiers::empty();

        // Parse leading pointers and their qualifiers
        while self.matches(&[TokenKind::Star]) {
            self.advance(); // Consume '*'
            _current_qualifiers = self.parse_type_qualifiers()?;
            declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
            _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
        }

        // Parse direct declarator (identifier or parenthesized declarator)
        let base_declarator = if self.matches(&[TokenKind::LeftParen]) {
            self.advance(); // Consume '('
            let inner_declarator = self.parse_declarator(None)?;
            self.expect(TokenKind::RightParen)?; // Consume ')'
            inner_declarator
        } else if let Some(ident_symbol) = initial_declarator {
            Declarator::Identifier(ident_symbol, TypeQualifiers::empty(), None)
        } else if let Some(token) = self.try_current_token() {
            if let TokenKind::Identifier(symbol) = token.kind {
                self.advance(); // Consume identifier
                Declarator::Identifier(symbol, TypeQualifiers::empty(), None)
            } else if self.is_abstract_declarator_start() {
                self.parse_abstract_declarator()?
            } else {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![
                        TokenKind::Star,
                        TokenKind::LeftParen,
                        TokenKind::LeftBracket,
                        TokenKind::Identifier(Symbol::new("")),
                    ],
                    found: token.kind,
                    location: token.location,
                });
            }
        } else {
            return Err(ParseError::SyntaxError {
                message: "Expected declarator".to_string(),
                location: SourceSpan::empty(),
            });
        };

        // Parse trailing array and function declarators
        let mut current_base = base_declarator;
        loop {
            if self.matches(&[TokenKind::LeftBracket]) {
                // Array declarator
                self.advance(); // Consume '['
                let array_size = self.parse_array_size()?;
                self.expect(TokenKind::RightBracket)?; // Consume ']'
                current_base = Declarator::Array(Box::new(current_base), array_size);
            } else if self.matches(&[TokenKind::LeftParen]) {
                // Function declarator
                self.advance(); // Consume '('
                let parameters = self.parse_function_parameters()?;
                self.expect(TokenKind::RightParen)?; // Consume ')'
                current_base = Declarator::Function(Box::new(current_base), parameters);
            } else {
                break;
            }
        }

        // Reconstruct the declarator chain in reverse order
        let mut final_declarator = current_base;
        for component in declarator_chain.into_iter().rev() {
            final_declarator = match component {
                DeclaratorComponent::Pointer(qualifiers) => {
                    Declarator::Pointer(qualifiers, Some(Box::new(final_declarator)))
                }
            };
        }

        Ok(final_declarator)
    }

    /// Helper to parse type qualifiers
    fn parse_type_qualifiers(&mut self) -> Result<TypeQualifiers, ParseError> {
        let mut qualifiers = TypeQualifiers::empty();
        while let Some(token) = self.try_current_token() {
            match token.kind {
                TokenKind::Const => {
                    qualifiers.insert(TypeQualifiers::CONST);
                    self.advance();
                }
                TokenKind::Volatile => {
                    qualifiers.insert(TypeQualifiers::VOLATILE);
                    self.advance();
                }
                TokenKind::Restrict => {
                    qualifiers.insert(TypeQualifiers::RESTRICT);
                    self.advance();
                }
                TokenKind::Atomic => {
                    qualifiers.insert(TypeQualifiers::ATOMIC);
                    self.advance();
                }
                _ => break,
            }
        }
        Ok(qualifiers)
    }

    /// Helper to parse array size
    fn parse_array_size(&mut self) -> Result<ArraySize, ParseError> {
        let is_static = self.accept(TokenKind::Static).is_some();
        let qualifiers = self.parse_type_qualifiers()?;

        if self.matches(&[TokenKind::Star]) {
            self.advance();
            Ok(ArraySize::Star { qualifiers })
        } else if self.matches(&[TokenKind::RightBracket]) {
            // Empty []
            Ok(ArraySize::Incomplete)
        } else {
            // Assume it's an expression for the size
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(expr_node) => {
                    if is_static || !qualifiers.is_empty() {
                        Ok(ArraySize::VlaSpecifier { is_static, qualifiers, size: Some(expr_node) })
                    } else {
                        Ok(ArraySize::Expression { expr: expr_node, qualifiers })
                    }
                }
                _ => Err(ParseError::SyntaxError {
                    message: "Expected array size expression".to_string(),
                    location: self.current_token().unwrap().location,
                }),
            }
        }
    }

    /// Helper to parse function parameters
    fn parse_function_parameters(&mut self) -> Result<Vec<ParamData>, ParseError> {
        let mut params = Vec::new();

        if !self.matches(&[TokenKind::RightParen]) {
            if self.matches(&[TokenKind::Void]) {
                // void parameter list
                self.advance();
            } else {
                loop {
                    if self.matches(&[TokenKind::Ellipsis]) {
                        // Variadic function
                        self.advance();
                        break;
                    }

                    // Parse declaration specifiers for this parameter
                    let start_idx = self.current_idx;
                    let saved_diagnostic_count = self.diag.diagnostics.len();

                    let specifiers = match self.parse_declaration_specifiers() {
                        Ok(specifiers) => {
                            debug!(
                                "parse_function_parameters: successfully parsed specifiers, current token: {:?}",
                                self.current_token_kind()
                            );
                            specifiers
                        }
                        Err(_e) => {
                            // If specifier parsing fails, we might be at a position where we need
                            // to fall back to parsing without a proper declarator
                            debug!(
                                "parse_function_parameters: specifier parsing failed, rolling back"
                            );
                            self.current_idx = start_idx;
                            self.diag.diagnostics.truncate(saved_diagnostic_count);

                            // Create a simple default specifier
                            vec![DeclSpecifier {
                                storage_class: None,
                                type_qualifiers: TypeQualifiers::empty(),
                                function_specifiers: FunctionSpecifiers::empty(),
                                alignment_specifier: None,
                                type_specifier: TypeSpecifier::Int,
                            }]
                        }
                    };

                    // Try to parse declarator, but be more careful about failures
                    let declarator = if !self.matches(&[TokenKind::Comma])
                        && !self.matches(&[TokenKind::RightParen])
                        && !self.matches(&[TokenKind::Ellipsis])
                    {
                        // Check if we can even attempt declarator parsing
                        let can_parse_declarator = self
                            .current_token_kind()
                            .map(|k| {
                                matches!(
                                    k,
                                    TokenKind::Identifier(_)
                                        | TokenKind::Star
                                        | TokenKind::LeftParen
                                        | TokenKind::LeftBracket
                                )
                            })
                            .unwrap_or(false);

                        if can_parse_declarator {
                            match self.parse_declarator(None) {
                                Ok(declarator) => Some(declarator),
                                Err(e) => {
                                    debug!(
                                        "parse_function_parameters: declarator parsing failed: {:?}",
                                        e
                                    );
                                    // If declarator parsing fails, we still want to continue
                                    // with a None declarator
                                    None
                                }
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    params.push(ParamData {
                        specifiers,
                        declarator,
                    });

                    if !self.matches(&[TokenKind::Comma]) {
                        break;
                    }
                    self.advance(); // consume comma
                }
            }
        }

        Ok(params)
    }

    /// Parse a statement
    pub fn parse_statement(&mut self) -> Result<NodeRef, ParseError> {
        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected statement".to_string(),
                location: SourceSpan::empty(),
            })?;

        // Check for label: identifier :
        if let TokenKind::Identifier(label_symbol) = token.kind
            && let Some(next_token) = self.peek_token(0)
            && next_token.kind == TokenKind::Colon
        {
            return self.parse_label_statement(label_symbol);
        }

        match token.kind {
            TokenKind::LeftBrace => {
                let (node, _) = self.parse_compound_statement()?;
                Ok(node)
            }
            TokenKind::If => self.parse_if_statement(),
            TokenKind::Switch => self.parse_switch_statement(),
            TokenKind::While => self.parse_while_statement(),
            TokenKind::Do => self.parse_do_while_statement(),
            TokenKind::For => self.parse_for_statement(),
            TokenKind::Goto => self.parse_goto_statement(),
            TokenKind::Continue => self.parse_continue_statement(),
            TokenKind::Break => self.parse_break_statement(),
            TokenKind::Return => self.parse_return_statement(),
            TokenKind::Semicolon => self.parse_empty_statement(),
            TokenKind::Case => self.parse_case_statement(),
            TokenKind::Default => self.parse_default_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    /// Parse compound statement (block)
    fn parse_compound_statement(&mut self) -> Result<(NodeRef, SourceLoc), ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::LeftBrace)?;

        let mut block_items = Vec::new();

        while !self.matches(&[TokenKind::RightBrace]) {
            let initial_idx = self.current_idx;

            debug!(
                "parse_compound_statement: parsing block item, current token {:?}, position {}",
                self.current_token_kind(),
                initial_idx
            );

            // Try parsing as declaration first, but only if it looks like a declaration start
            let should_try_declaration = self.is_declaration_start();
            let mut declaration_attempt: Option<Result<NodeRef, ParseError>> = None;

            if should_try_declaration {
                // Save state before attempting declaration parsing
                let saved_idx = self.current_idx;
                let saved_error_state = self.diag.diagnostics.len();

                debug!(
                    "parse_compound_statement: trying declaration parsing at position {}",
                    saved_idx
                );
                match self.parse_declaration() {
                    Ok(declaration) => {
                        debug!("parse_compound_statement: successfully parsed declaration");
                        block_items.push(declaration);
                    }
                    Err(decl_error) => {
                        debug!(
                            "parse_compound_statement: declaration parsing failed: {:?}, rolling back from {} to {}",
                            decl_error, self.current_idx, saved_idx
                        );
                        // Reset state and try as statement
                        self.current_idx = saved_idx;
                        // Remove any diagnostics added during failed declaration parsing
                        self.diag.diagnostics.truncate(saved_error_state);
                        declaration_attempt = Some(Err(decl_error));
                    }
                }
            }

            // If declaration failed or wasn't attempted, try as statement
            if declaration_attempt.is_some() || !should_try_declaration {
                if declaration_attempt.is_some() {
                    debug!(
                        "parse_compound_statement: reset to position {}, trying statement",
                        initial_idx
                    );
                } else {
                    debug!("parse_compound_statement: not a declaration start, trying statement");
                }

                match self.parse_statement() {
                    Ok(statement) => {
                        debug!("parse_compound_statement: successfully parsed statement");
                        block_items.push(statement);
                    }
                    Err(stmt_error) => {
                        debug!(
                            "parse_compound_statement: statement parsing also failed: {:?}",
                            stmt_error
                        );
                        // Both declaration and statement parsing failed
                        // Report the declaration error and try to synchronize
                        if let Some(Err(decl_error)) = declaration_attempt {
                            self.diag.report_parse_error(decl_error);
                        } else {
                            self.diag.report_parse_error(stmt_error);
                        }
                        self.synchronize();
                    }
                }
            }
        }

        let right_brace_token = self.expect(TokenKind::RightBrace)?;
        let end_span = right_brace_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::CompoundStatement(block_items), span));
        Ok((node, end_span))
    }

    /// Check if current tokens indicate start of a declaration
    fn is_declaration_start(&self) -> bool {
        debug!(
            "is_declaration_start: checking token {:?}",
            self.current_token_kind()
        );
        if let Some(token) = self.try_current_token() {
            match token.kind {
                TokenKind::Typedef
                | TokenKind::Extern
                | TokenKind::Static
                | TokenKind::Auto
                | TokenKind::Register
                | TokenKind::ThreadLocal
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic
                | TokenKind::Inline
                | TokenKind::Noreturn
                | TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum
                | TokenKind::Alignas => true,
                TokenKind::Identifier(symbol) => {
                    // Check if it's a typedef name
                    let is_type = self.is_type_name(symbol);
                    debug!(
                        "is_declaration_start: identifier {:?}, is_type_name={}",
                        symbol, is_type
                    );
                    is_type
                }
                // Exclude sizeof and other expression-only keywords that might be mistaken for type names
                TokenKind::Sizeof | TokenKind::Alignof | TokenKind::Generic => false,
                _ => false,
            }
        } else {
            false
        }
    }

    /// Parse if statement
    fn parse_if_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::If)?;
        self.expect(TokenKind::LeftParen)?;

        let condition_result = self.parse_expression(BindingPower::MIN)?;
        let condition = match condition_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in if condition".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::RightParen)?;

        let then_branch = self.parse_statement()?;

        let else_branch = if self.matches(&[TokenKind::Else]) {
            self.advance(); // consume 'else'
            Some(self.parse_statement()?)
        } else {
            None
        };

        let end_span = match &else_branch {
            Some(else_stmt) => self.ast.get_node(*else_stmt).span.end,
            None => self.ast.get_node(then_branch).span.end,
        };

        let span = SourceSpan::new(start_span, end_span);

        let if_stmt = IfStmt {
            condition,
            then_branch,
            else_branch,
        };

        let node = self.ast.push_node(Node::new(NodeKind::If(if_stmt), span));
        Ok(node)
    }

    /// Parse switch statement
    fn parse_switch_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Switch)?;
        self.expect(TokenKind::LeftParen)?;

        let condition_result = self.parse_expression(BindingPower::MIN)?;
        let condition = match condition_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in switch condition".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::RightParen)?;

        trace!("parse_for_statement: parsing body");

        let body = self.parse_statement()?;

        let end_span = self.ast.get_node(body).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node {
            kind: NodeKind::Switch(condition, body),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse while statement
    fn parse_while_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::While)?;
        self.expect(TokenKind::LeftParen)?;

        let condition_result = self.parse_expression(BindingPower::MIN)?;
        let condition = match condition_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in while condition".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::RightParen)?;

        let body = self.parse_statement()?;

        let end_span = self.ast.get_node(body).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let while_stmt = WhileStmt { condition, body };

        let node = self
            .ast
            .push_node(Node::new(NodeKind::While(while_stmt), span));
        Ok(node)
    }

    /// Parse do-while statement
    fn parse_do_while_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Do)?;

        let body = self.parse_statement()?;

        self.expect(TokenKind::While)?;
        self.expect(TokenKind::LeftParen)?;

        let condition_result = self.parse_expression(BindingPower::MIN)?;
        let condition = match condition_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in do-while condition".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::RightParen)?;
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node {
            kind: NodeKind::DoWhile(body, condition),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse for statement
    fn parse_for_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::For)?;
        self.expect(TokenKind::LeftParen)?;

        trace!("parse_for_statement: parsing initialization");

        // Parse initialization
        let init = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else if self.is_declaration_start() {
            trace!("parse_for_statement: parsing declaration in init");
            // Parse declaration specifiers
            let specifiers = self.parse_declaration_specifiers()?;
            // Parse declarator
            let declarator = self.parse_declarator(None)?;
            // Parse initializer if present
            let initializer = if self.matches(&[TokenKind::Assign]) {
                self.advance(); // consume '='
                Some(self.parse_initializer()?)
            } else {
                None
            };

            let init_declarator = InitDeclarator {
                declarator,
                initializer,
            };

            let declaration_data = DeclarationData {
                specifiers,
                init_declarators: vec![init_declarator],
            };

            // Don't consume semicolon here - it will be consumed by the normal for loop flow
            let span = SourceSpan::new(start_span, self.current_token().unwrap().location.end);

            Some(
                self.ast
                    .push_node(Node::new(NodeKind::Declaration(declaration_data), span)),
            )
        } else {
            trace!("parse_for_statement: parsing expression in init");
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression or declaration in for init".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        self.expect(TokenKind::Semicolon)?;

        trace!("parse_for_statement: parsing condition");

        // Parse condition
        let condition = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else {
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in for condition".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        self.expect(TokenKind::Semicolon)?;

        trace!("parse_for_statement: parsing increment");

        // Parse increment
        let increment = if self.matches(&[TokenKind::RightParen]) {
            None
        } else {
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in for increment".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        self.expect(TokenKind::RightParen)?;

        let body = self.parse_statement()?;

        let end_span = self.ast.get_node(body).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let for_stmt = ForStmt {
            init,
            condition,
            increment,
            body,
        };

        let node = self.ast.push_node(Node::new(NodeKind::For(for_stmt), span));
        Ok(node)
    }

    /// Parse goto statement
    fn parse_goto_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Goto)?;

        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected label name".to_string(),
                location: SourceSpan::empty(),
            })?;

        let label = match token.kind {
            TokenKind::Identifier(symbol) => symbol,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![TokenKind::Identifier(Symbol::new(""))],
                    found: token.kind,
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.advance();
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Goto(label), span));
        Ok(node)
    }

    /// Parse continue statement
    fn parse_continue_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Continue)?;
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Continue, span));
        Ok(node)
    }

    /// Parse break statement
    fn parse_break_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        self.expect(TokenKind::Break)?;
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Break, span));
        Ok(node)
    }

    /// Parse return statement
    fn parse_return_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        let _return_token = self.expect(TokenKind::Return)?;
        debug!("parse_return_statement: parsing return expression");

        let value = if self.matches(&[TokenKind::Semicolon]) {
            debug!("parse_return_statement: empty return");
            None
        } else {
            debug!(
                "parse_return_statement: parsing return expression with current token {:?}",
                self.current_token_kind()
            );
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            debug!("parse_return_statement: parsed expression successfully");
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in return statement".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Return(value), span));
        Ok(node)
    }

    /// Parse empty statement
    fn parse_empty_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::EmptyStatement, span));
        Ok(node)
    }

    /// Parse case statement (including GNU case ranges)
    fn parse_case_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        self.expect(TokenKind::Case)?;

        let start_expr_result = self.parse_expression(BindingPower::MIN)?;
        let start_expr = match start_expr_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected constant expression in case".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        // Check for GNU case range extension: case 1 ... 10:
        let (end_expr, is_range) = if self.matches(&[TokenKind::Ellipsis]) {
            self.advance(); // consume '...'
            let end_expr_result = self.parse_expression(BindingPower::MIN)?;
            let end_expr = match end_expr_result {
                ParseExprOutput::Expression(node) => node,
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected constant expression after '...' in case range"
                            .to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            };
            (Some(end_expr), true)
        } else {
            (None, false)
        };

        self.expect(TokenKind::Colon)?;

        let statement = self.parse_statement()?;

        let end_span = self.ast.get_node(statement).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = if is_range {
            self.ast.push_node(Node {
                kind: NodeKind::CaseRange(start_expr, end_expr.unwrap(), statement),
                span,
                resolved_type: Cell::new(None),
                resolved_symbol: Cell::new(None),
            })
        } else {
            self.ast.push_node(Node {
                kind: NodeKind::Case(start_expr, statement),
                span,
                resolved_type: Cell::new(None),
                resolved_symbol: Cell::new(None),
            })
        };
        Ok(node)
    }

    /// Parse default statement
    fn parse_default_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        self.expect(TokenKind::Default)?;
        self.expect(TokenKind::Colon)?;

        let statement = self.parse_statement()?;
        let end_span = self.ast.get_node(statement).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::Default(statement), span));
        Ok(node)
    }

    /// Parse label statement
    fn parse_label_statement(&mut self, label_symbol: Symbol) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        self.advance(); // consume the identifier
        self.expect(TokenKind::Colon)?; // consume the colon

        let statement = self.parse_statement()?;
        let end_span = self.ast.get_node(statement).span.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::Label(label_symbol, statement), span));
        Ok(node)
    }

    /// Parse expression statement
    fn parse_expression_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        let expression = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else {
            // Try to parse expression, but handle parsing failures gracefully
            match self.parse_expression(BindingPower::MIN) {
                Ok(ParseExprOutput::Expression(node)) => Some(node),
                Ok(_) => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in expression statement".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
                Err(e) => {
                    // If expression parsing fails, try to at least consume the semicolon
                    // to avoid infinite loops
                    if self.matches(&[TokenKind::Semicolon]) {
                        None
                    } else {
                        return Err(e);
                    }
                }
            }
        };

        // Always expect a semicolon
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::ExpressionStatement(expression), span));
        Ok(node)
    }

    /// Parse function definition
    pub fn parse_function_definition(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;

        // Parse declaration specifiers
        let specifiers = self.parse_declaration_specifiers()?;

        // Parse declarator (should be a function declarator)
        let declarator = self.parse_declarator(None)?;

        // Parse function body
        let (body, body_end_span) = self.parse_compound_statement()?;

        let span = SourceSpan::new(start_span, body_end_span);

        let function_def = FunctionDefData {
            specifiers,
            declarator,
            body,
        };

        let node = self
            .ast
            .push_node(Node::new(NodeKind::FunctionDef(function_def), span));
        Ok(node)
    }

    /// Parse translation unit (top level)
    pub fn parse_translation_unit(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        let mut end_span = SourceLoc::empty();

        let mut top_level_declarations = Vec::new();
        let mut iteration_count = 0;
        const MAX_ITERATIONS: usize = 1000; // Prevent infinite loops

        while let Some(token) = self.try_current_token() {
            if token.kind == TokenKind::EndOfFile {
                end_span = token.location.end;
                break;
            }

            // Prevent infinite loops by limiting iterations
            iteration_count += 1;
            if iteration_count > MAX_ITERATIONS {
                debug!(
                    "Parser exceeded maximum iteration limit at token {:?}, position {}",
                    token.kind, self.current_idx
                );
                return Err(ParseError::SyntaxError {
                    message: format!(
                        "Parser exceeded maximum iteration limit - possible infinite loop at token {:?}",
                        token.kind
                    ),
                    location: token.location,
                });
            }

            let initial_idx = self.current_idx;

            // Try parsing as declaration first
            match self.parse_declaration() {
                Ok(declaration) => {
                    top_level_declarations.push(declaration);
                }
                Err(_) => {
                    // If declaration parsing failed, try function definition
                    // Reset to initial position for backtracking
                    self.current_idx = initial_idx;
                    match self.parse_function_definition() {
                        Ok(func_def) => {
                            top_level_declarations.push(func_def);
                        }
                        Err(e) => {
                            self.diag.report_parse_error(e);
                            self.synchronize();
                        }
                    }
                }
            }
        }

        let span = SourceSpan::new(start_span, end_span);
        let node = self.ast.push_node(Node::new(
            NodeKind::TranslationUnit(top_level_declarations),
            span,
        ));

        self.ast.set_root_node(node);

        Ok(node)
    }

    /// Check if current tokens indicate start of a function definition
    #[allow(dead_code)]
    fn is_function_definition_start(&self) -> bool {
        // Function definitions start with declaration specifiers like declarations,
        // but we distinguish them during parsing by trying declaration first
        false // Always try declaration first, then function definition if failed
    }

    /// Parse _Generic selection (C11)
    pub fn parse_generic_selection(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Generic)?;
        self.expect(TokenKind::LeftParen)?;

        let controlling_expr_result = self.parse_expression(BindingPower::MIN)?;
        let controlling_expr = match controlling_expr_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in _Generic controlling expression".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::Comma)?;

        let mut associations = Vec::new();

        loop {
            let type_name = if self.matches(&[TokenKind::Default]) {
                self.advance(); // consume 'default'
                None
            } else {
                Some(self.parse_type_name()?)
            };

            self.expect(TokenKind::Colon)?;

            let result_expr_result = self.parse_expression(BindingPower::MIN)?;
            let result_expr = match result_expr_result {
                ParseExprOutput::Expression(node) => node,
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in _Generic association".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            };

            associations.push(GenericAssociation {
                type_name,
                result_expr,
            });

            if !self.matches(&[TokenKind::Comma]) {
                break;
            }
            self.advance(); // consume comma
        }

        let right_paren_token = self.expect(TokenKind::RightParen)?;

        let end_span = right_paren_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node {
            kind: NodeKind::GenericSelection(controlling_expr, associations),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse compound literal (C99)
    pub fn parse_compound_literal(&mut self) -> Result<NodeRef, ParseError> {
        let start_token = self.expect(TokenKind::LeftParen)?;
        let type_ref = self.parse_type_name()?;
        self.expect(TokenKind::RightParen)?;

        self.parse_compound_literal_from_type_and_start(type_ref, start_token.location.start)
    }

    /// Parse compound literal given the type and start location
    fn parse_compound_literal_from_type_and_start(&mut self, type_ref: TypeRef, start_loc: SourceLoc) -> Result<NodeRef, ParseError> {
        let initializer = self.parse_initializer()?;

        let end_loc = self.current_token_span()?.end;
        let span = SourceSpan {
            start: start_loc,
            end: end_loc,
        };

        let initializer_ref = self.ast.push_initializer(initializer);
        let node = self.ast.push_node(Node {
            kind: NodeKind::CompoundLiteral(type_ref, initializer_ref),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }


    /// Parse static assert (C11)
    pub fn parse_static_assert(&mut self, start_token: Token) -> Result<NodeRef, ParseError> {
        // already consumed `_Static_assert`
        let start_span = start_token.location.start;
        self.expect(TokenKind::LeftParen)?;

        let condition_result = self.parse_expression(BindingPower::MIN)?;
        let condition = match condition_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in _Static_assert condition".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::Comma)?;

        let token = self
            .try_current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected string literal in _Static_assert".to_string(),
                location: SourceSpan::empty(),
            })?;

        let message = match token.kind {
            TokenKind::StringLiteral(symbol) => symbol,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![TokenKind::StringLiteral(Symbol::new(""))],
                    found: token.kind,
                    location: token.location,
                });
            }
        };

        self.advance();
        self.expect(TokenKind::RightParen)?;
        let semicolon_token = self.expect(TokenKind::Semicolon)?;
        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node {
            kind: NodeKind::StaticAssert(condition, message),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse sizeof expression or type
    pub fn parse_sizeof(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        debug!(
            "parse_sizeof: starting at position {}, token {:?}",
            self.current_idx,
            self.current_token_kind()
        );

        self.expect(TokenKind::Sizeof)?;
        debug!(
            "parse_sizeof: consumed sizeof token, now at position {}, token {:?}",
            self.current_idx,
            self.current_token_kind()
        );

        let node = if self.matches(&[TokenKind::LeftParen]) {
            self.advance(); // consume '('
            debug!(
                "parse_sizeof: found '(', now at position {}, token {:?}",
                self.current_idx,
                self.current_token_kind()
            );

            // Check if it's a type name or expression
            if self.is_type_name_start() {
                debug!("parse_sizeof: detected type name start, parsing type name");
                let type_ref = self.parse_type_name()?;
                debug!(
                    "parse_sizeof: parsed type name, now at position {}, token {:?}",
                    self.current_idx,
                    self.current_token_kind()
                );

                let right_paren_token = self.expect(TokenKind::RightParen)?;

                let end_span = right_paren_token.location.end;
                let span = SourceSpan::new(start_span, end_span);

                debug!("parse_sizeof: successfully parsed sizeof(type)");
                self.ast
                    .push_node(Node::new(NodeKind::SizeOfType(type_ref), span))
            } else {
                debug!("parse_sizeof: detected expression, parsing expression");
                let expr_result = self.parse_expression(BindingPower::MIN)?;
                let expr = match expr_result {
                    ParseExprOutput::Expression(node) => node,
                    _ => {
                        return Err(ParseError::SyntaxError {
                            message: "Expected expression in sizeof".to_string(),
                            location: self.current_token().unwrap().location,
                        });
                    }
                };
                let right_paren_token = self.expect(TokenKind::RightParen)?;

                let end_span = right_paren_token.location.end;
                let span = SourceSpan::new(start_span, end_span);

                debug!("parse_sizeof: successfully parsed sizeof(expression)");
                self.ast
                    .push_node(Node::new(NodeKind::SizeOfExpr(expr), span))
            }
        } else {
            debug!("parse_sizeof: no '(', parsing unary expression");
            let expr_result = self.parse_expression(BindingPower::UNARY)?;
            let expr = match expr_result {
                ParseExprOutput::Expression(node) => node,
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in sizeof".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            };

            let end_span = self.ast.get_node(expr).span.end;
            let span = SourceSpan::new(start_span, end_span);

            debug!("parse_sizeof: successfully parsed sizeof unary expression");
            self.ast
                .push_node(Node::new(NodeKind::SizeOfExpr(expr), span))
        };

        Ok(node)
    }

    /// Parse _Alignof (C11)
    pub fn parse_alignof(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self.current_token()?.location.start;
        self.expect(TokenKind::Alignof)?;
        self.expect(TokenKind::LeftParen)?;

        let type_ref = self.parse_type_name()?;
        let right_paren_token = self.expect(TokenKind::RightParen)?;

        let end_span = right_paren_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::AlignOf(type_ref), span));
        Ok(node)
    }

    /// Check if current token starts a type name
    fn is_type_name_start(&self) -> bool {
        debug!(
            "is_type_name_start: checking token {:?} at position {}",
            self.current_token_kind(),
            self.current_idx
        );

        if let Some(token) = self.try_current_token() {
            let result = matches!(
                token.kind,
                TokenKind::Void
                    | TokenKind::Char
                    | TokenKind::Short
                    | TokenKind::Int
                    | TokenKind::Long
                    | TokenKind::Float
                    | TokenKind::Double
                    | TokenKind::Signed
                    | TokenKind::Unsigned
                    | TokenKind::Bool
                    | TokenKind::Complex
                    | TokenKind::Struct
                    | TokenKind::Union
                    | TokenKind::Enum
                    | TokenKind::Const
                    | TokenKind::Volatile
                    | TokenKind::Restrict
                    | TokenKind::Atomic
            );

            // For identifiers, only consider them type name starts if they are actually typedef names
            let is_identifier_type = if let TokenKind::Identifier(symbol) = token.kind {
                self.is_type_name(symbol)
            } else {
                false
            };

            let final_result = result || is_identifier_type;

            debug!(
                "is_type_name_start: token {:?} is type name start: {} (direct: {}, identifier: {})",
                token.kind, final_result, result, is_identifier_type
            );
            final_result
        } else {
            debug!("is_type_name_start: no token available");
            false
        }
    }

    /// Check if current token starts an abstract declarator
    fn is_abstract_declarator_start(&self) -> bool {
        if let Some(token) = self.try_current_token() {
            match token.kind {
                TokenKind::Star => true,        // pointer
                TokenKind::LeftParen => true,   // parenthesized abstract declarator
                TokenKind::LeftBracket => true, // array
                _ => false,
            }
        } else {
            false
        }
    }

    /// Extract the declared name from a declarator, if any
    fn get_declarator_name(&self, declarator: &Declarator) -> Option<Symbol> {
        match declarator {
            Declarator::Identifier(name, _, _) => Some(*name),
            Declarator::Pointer(_, Some(inner)) => self.get_declarator_name(inner),
            Declarator::Array(inner, _) => self.get_declarator_name(inner),
            Declarator::Function(inner, _) => self.get_declarator_name(inner),
            Declarator::AnonymousRecord(_, _) => None,
            Declarator::Abstract => None,
            Declarator::Pointer(_, None) => None,
        }
    }

    /// Parse abstract declarator (for type names without identifiers)
    fn parse_abstract_declarator(&mut self) -> Result<Declarator, ParseError> {
        let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
        let mut _current_qualifiers = TypeQualifiers::empty();

        // Parse leading pointers and their qualifiers
        while self.matches(&[TokenKind::Star]) {
            self.advance(); // Consume '*'
            _current_qualifiers = self.parse_type_qualifiers()?;
            declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
            _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
        }

        // Parse direct abstract declarator (parenthesized or array/function)
        let base_declarator = if self.matches(&[TokenKind::LeftParen]) {
            self.advance(); // Consume '('
            let inner_declarator = self.parse_abstract_declarator()?;
            self.expect(TokenKind::RightParen)?; // Consume ')'
            inner_declarator
        } else {
            Declarator::Abstract
        };

        // Parse trailing array and function declarators
        let mut current_base = base_declarator;
        loop {
            if self.matches(&[TokenKind::LeftBracket]) {
                // Array declarator
                self.advance(); // Consume '['
                let array_size = self.parse_array_size()?;
                self.expect(TokenKind::RightBracket)?; // Consume ']'
                current_base = Declarator::Array(Box::new(current_base), array_size);
            } else if self.matches(&[TokenKind::LeftParen]) {
                // Function declarator
                self.advance(); // Consume '('
                let parameters = self.parse_function_parameters()?;
                self.expect(TokenKind::RightParen)?; // Consume ')'
                current_base = Declarator::Function(Box::new(current_base), parameters);
            } else {
                break;
            }
        }

        // Reconstruct the declarator chain in reverse order
        let mut final_declarator = current_base;
        for component in declarator_chain.into_iter().rev() {
            final_declarator = match component {
                DeclaratorComponent::Pointer(qualifiers) => {
                    Declarator::Pointer(qualifiers, Some(Box::new(final_declarator)))
                }
            };
        }

        Ok(final_declarator)
    }

    /// Disambiguates between a type name and an identifier in ambiguous contexts.
    /// This is crucial for parsing C's "declaration-specifier-list" vs "expression" ambiguity.
    fn is_type_name(&self, symbol: Symbol) -> bool {
        let result = self.typedef_names.contains(&symbol);

        debug!(
            "is_type_name: checking symbol {:?}, result={}, typedef_names={:?}",
            symbol, result, self.typedef_names
        );
        result
    }

    /// Check if a cast expression starts at the current position
    /// This is called after consuming an opening parenthesis
    fn is_cast_expression_start(&self) -> bool {
        debug!(
            "is_cast_expression_start: checking at position {}, token {:?}",
            self.current_idx,
            self.current_token_kind()
        );

        if let Some(token) = self.try_current_token() {
            match token.kind {
                // Direct type specifiers
                TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                | TokenKind::Atomic
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict => {
                    debug!(
                        "is_cast_expression_start: found direct type specifier: {:?}",
                        token.kind
                    );
                    true
                }
                TokenKind::Star => {
                    // Could be a pointer to a type, look further
                    debug!("is_cast_expression_start: found Star, looking ahead");
                    self.is_cast_expression_start_advanced()
                }
                TokenKind::Identifier(symbol) => {
                    // Could be a typedef name
                    let is_type = self.is_type_name(symbol);
                    debug!(
                        "is_cast_expression_start: found identifier {:?}, is_type={}",
                        symbol, is_type
                    );
                    is_type
                }
                _ => {
                    debug!(
                        "is_cast_expression_start: token {:?} not recognized as cast start",
                        token.kind
                    );
                    false
                }
            }
        } else {
            debug!("is_cast_expression_start: no token available");
            false
        }
    }

    /// Helper for more complex cast expression detection
    fn is_cast_expression_start_advanced(&self) -> bool {
        // Look ahead to see if we have a type pattern
        let mut idx = self.current_idx;

        // Skip stars (pointers)
        while let Some(token) = self.tokens.get(idx) {
            if token.kind == TokenKind::Star {
                idx += 1;
                continue;
            }
            break;
        }

        // After pointers, look for type qualifiers
        while let Some(token) = self.tokens.get(idx) {
            match token.kind {
                TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic => {
                    idx += 1;
                    continue;
                }
                _ => break,
            }
        }

        // Finally, check for a type name
        if let Some(token) = self.tokens.get(idx) {
            match token.kind {
                TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum => true,
                TokenKind::Identifier(symbol) => self.is_type_name(symbol),
                _ => false,
            }
        } else {
            false
        }
    }


    /// Parse cast expression given the already parsed type and right paren token
    fn parse_cast_expression_from_type_and_paren(&mut self, type_ref: TypeRef, right_paren_token: Token) -> Result<NodeRef, ParseError> {
        // Parse the expression being cast
        let expr_result = self.parse_expression(BindingPower::CAST)?;
        let expr_node = match expr_result {
            ParseExprOutput::Expression(node) => {
                debug!("parse_cast_expression: parsed operand expression");
                node
            }
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression after cast".to_string(),
                    location: right_paren_token.location,
                });
            }
        };

        let span = SourceSpan::new(
            right_paren_token.location.start, // Start from the opening paren
            self.ast.get_node(expr_node).span.end,
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::Cast(type_ref, expr_node),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });

        debug!("parse_cast_expression: successfully parsed cast expression");
        Ok(node)
    }

}
