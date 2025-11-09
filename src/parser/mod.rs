use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, ParseError};
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
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
    in_function_body: bool,
    in_struct_declaration: bool,
    in_enum_declaration: bool,

    // Error recovery state
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
        Parser {
            tokens,
            current_idx: 0,
            ast,
            diag,
            in_function_body: false,
            in_struct_declaration: false,
            in_enum_declaration: false,
            error_recovery_points: Vec::new(),
            typedef_names: HashSet::new(),
        }
    }

    /// Get the current token
    fn current_token(&self) -> Option<Token> {
        self.tokens.get(self.current_idx).cloned()
    }

    /// Get the current token kind
    fn current_token_kind(&self) -> Option<TokenKind> {
        self.current_token().map(|t| t.kind)
    }

    /// Peek at the next token without consuming it
    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.current_idx + 1)
    }

    /// Peek at the next token kind
    fn peek_token_kind(&self) -> Option<TokenKind> {
        self.peek_token().map(|t| t.kind)
    }

    /// Advance to the next token
    fn advance(&mut self) -> Option<Token> {
        if self.current_idx < self.tokens.len() {
            let token = &self.tokens[self.current_idx];
            self.current_idx += 1;
            Some(token.clone())
        } else {
            None
        }
    }

    /// Expect a specific token kind, consume it if found
    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParseError> {
        if let Some(token) = self.current_token() {
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

        while let Some(token) = self.current_token() {
            match token.kind {
                TokenKind::LeftBrace => brace_depth += 1,
                TokenKind::RightBrace => {
                    brace_depth -= 1;
                    if brace_depth < 0 {
                        break; // Unmatched brace, stop here
                    }
                }
                TokenKind::LeftParen => paren_depth += 1,
                TokenKind::RightParen => {
                    paren_depth -= 1;
                    if paren_depth < 0 {
                        break; // Unmatched paren, stop here
                    }
                }
                TokenKind::Semicolon => {
                    if brace_depth == 0 && paren_depth == 0 {
                        self.advance();
                        break;
                    }
                }
                TokenKind::EndOfFile => break,
                _ => {}
            }
            self.advance();
        }
    }

    /// Parse an integer constant from token text
    fn parse_integer_constant(&self, text: Symbol) -> Result<i64, ParseError> {
        let token = self.current_token().unwrap();
        // C11 integer literal parsing: handle bases (decimal, octal, hex) and suffixes (u, l, ll)
        self.parse_c11_integer_literal(text)
    }

    /// Parse C11 integer literal syntax
    fn parse_c11_integer_literal(&self, text: Symbol) -> Result<i64, ParseError> {
        let text_str = text.as_str();
        let token = self.current_token().unwrap();

        // C11 integer literal format: [0[xX]][digits][suffix]
        // Suffixes: u/U (unsigned), l/L (long), ll/LL (long long)
        // Can be combined: ul, ull, etc.

        // Find where the suffix starts (if any)
        let mut end_of_digits = text_str.len();
        let mut has_unsigned = false;
        let mut has_long = false;
        let mut has_long_long = false;

        // Check for suffixes (case insensitive)
        let lower_text = text_str.to_lowercase();
        if lower_text.ends_with("ull") || lower_text.ends_with("llu") {
            end_of_digits = text_str.len() - 3;
            has_long_long = true;
            has_unsigned = lower_text.ends_with("ull");
        } else if lower_text.ends_with("ul") || lower_text.ends_with("lu") {
            end_of_digits = text_str.len() - 2;
            has_long = true;
            has_unsigned = lower_text.ends_with("ul");
        } else if lower_text.ends_with("u") {
            end_of_digits = text_str.len() - 1;
            has_unsigned = true;
        } else if lower_text.ends_with("ll") {
            end_of_digits = text_str.len() - 2;
            has_long_long = true;
        } else if lower_text.ends_with("l") {
            end_of_digits = text_str.len() - 1;
            has_long = true;
        }

        let digits_part = &text_str[..end_of_digits];

        // Determine base
        let (base, digits) = if digits_part.starts_with("0x") || digits_part.starts_with("0X") {
            (16, &digits_part[2..])
        } else if digits_part.starts_with("0") && digits_part.len() > 1 {
            (8, &digits_part[1..])
        } else {
            (10, digits_part)
        };

        // Parse the number
        let value = match base {
            16 => i64::from_str_radix(digits, 16),
            8 => i64::from_str_radix(digits, 8),
            10 => digits.parse::<i64>(),
            _ => unreachable!(),
        };

        match value {
            Ok(val) => Ok(val),
            Err(_) => Err(ParseError::InvalidIntegerConstant {
                text: text_str.to_string(),
                location: token.location,
            }),
        }
    }

    /// Parse C11 floating-point literal syntax
    fn parse_c11_float_literal(&self, text: Symbol) -> Result<f64, ParseError> {
        let text_str = text.as_str();
        let token = self.current_token().unwrap();

        // C11 floating-point literal format:
        // [digits][.digits][e|E[+|-]digits][f|F|l|L]
        // or [digits][e|E[+|-]digits][f|F|l|L]
        // or 0[xX][hexdigits][.hexdigits][p|P[+|-]digits][f|F|l|L]

        // Handle hexadecimal floating-point literals (C99/C11)
        if text_str.starts_with("0x") || text_str.starts_with("0X") {
            self.parse_hex_float_literal(text_str, token.location)
        } else {
            // Use Rust's built-in parsing for decimal floats
            match text_str.parse::<f64>() {
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
        let mut is_negative = false;
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
        if let Some(&c) = chars.peek() {
            if c == 'p' || c == 'P' {
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
                    message: format!("Invalid exponent '{}' in hexadecimal float literal", exp_str),
                    location,
                })?;

                if exp_negative {
                    exponent = -exponent;
                }
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

    /// Intern an identifier
    fn intern_identifier(&self, text: &str) -> Result<Symbol, ParseError> {
        Ok(Symbol::new(text))
    }

    /// Main expression parsing using Pratt algorithm
    pub fn parse_expression(
        &mut self,
        min_binding_power: BindingPower,
    ) -> Result<ParseExprOutput, ParseError> {
        let mut left = self.parse_prefix()?;

        loop {
            let current_token = match self.current_token() {
                Some(token) => token,
                None => break,
            };

            let Some((binding_power, associativity)) =
                PrattParser::get_binding_power(current_token.kind)
            else {
                break;
            };

            if binding_power < min_binding_power {
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
            let right = self.parse_infix(left, op_token, next_min_bp)?;
            let left_span = self.ast.get_node(left).span;
            let right_span = self.ast.get_node(right).span;
            let span = SourceSpan::new(left_span.start, right_span.end);
            left = self.ast.push_node(Node::new(
                NodeKind::BinaryOp(BinaryOp::Add, left, right), // Placeholder, will be fixed
                span,
            ));
        }

        Ok(ParseExprOutput::Expression(left))
    }

    /// Parse prefix expression
    fn parse_prefix(&mut self) -> Result<NodeRef, ParseError> {
        let token = self
            .current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?;

        match token.kind {
            TokenKind::Identifier(symbol) => {
                self.advance();
                let node = self.ast.push_node(Node {
                    kind: NodeKind::Ident(symbol, Cell::new(None)),
                    span: token.location,
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(node)
            }
            TokenKind::IntegerConstant(text) => {
                self.advance();
                let value = self.parse_integer_constant(text)?;
                let node = self.ast.push_node(Node {
                    kind: NodeKind::LiteralInt(text),
                    span: token.location,
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
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
                self.advance();
                let expr = self.parse_expression(BindingPower::MIN)?;
                self.expect(TokenKind::RightParen)?;
                match expr {
                    ParseExprOutput::Expression(node) => Ok(node),
                    _ => Err(ParseError::SyntaxError {
                        message: "Expected expression in parentheses".to_string(),
                        location: token.location,
                    }),
                }
            }
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Not
            | TokenKind::Increment
            | TokenKind::Decrement
            | TokenKind::Star
            | TokenKind::And => self.parse_unary_operator(token),
            TokenKind::Generic => return self.parse_generic_selection(),
            TokenKind::Alignof => return self.parse_alignof(),
            _ => Err(ParseError::UnexpectedToken {
                expected: vec![
                    TokenKind::Identifier(Symbol::new("")),
                    TokenKind::IntegerConstant(Symbol::new("0")),
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
            TokenKind::Increment => return self.parse_postfix_increment(left),
            TokenKind::Decrement => return self.parse_postfix_decrement(left),
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

        let node = self.ast.push_node(Node {
            kind: NodeKind::BinaryOp(op, left, right_node),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
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
        let mut args = Vec::new();

        if !self.matches(&[TokenKind::RightParen]) {
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

                if !self.matches(&[TokenKind::Comma]) {
                    break;
                }
                self.advance(); // consume comma
            }
        }

        self.expect(TokenKind::RightParen)?;

        let span = SourceSpan::new(
            self.ast.get_node(function).span.start,
            self.current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
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
        let index_result = self.parse_expression(BindingPower::MIN)?;
        let index = match index_result {
            ParseExprOutput::Expression(node) => node,
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression in array index".to_string(),
                    location: self.current_token().unwrap().location,
                });
            }
        };

        self.expect(TokenKind::RightBracket)?;

        let span = SourceSpan::new(
            self.ast.get_node(array).span.start,
            self.current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
        );

        let node = self.ast.push_node(Node {
            kind: NodeKind::IndexAccess(array, index),
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
            .current_token()
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
    fn parse_postfix_increment(&mut self, operand: NodeRef) -> Result<NodeRef, ParseError> {
        let span = SourceSpan::new(
            self.ast.get_node(operand).span.start,
            self.current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
        );

        let node = self
            .ast
            .push_node(Node::new(NodeKind::PostIncrement(operand), span));
        Ok(node)
    }

    /// Parse postfix decrement
    fn parse_postfix_decrement(&mut self, operand: NodeRef) -> Result<NodeRef, ParseError> {
        let span = SourceSpan::new(
            self.ast.get_node(operand).span.start,
            self.current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
        );

        let node = self
            .ast
            .push_node(Node::new(NodeKind::PostDecrement(operand), span));
        Ok(node)
    }

    /// Parse a declaration
    pub fn parse_declaration(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));

        // Check for _Static_assert (C11)
        if self.matches(&[TokenKind::StaticAssert]) {
            return self.parse_static_assert();
        }

        // Parse declaration specifiers
        let specifiers = self.parse_declaration_specifiers()?;

        // Parse init declarators
        let mut init_declarators = Vec::new();

        // Check if we have declarators (not just specifiers like "int;")
        if !self.matches(&[TokenKind::Semicolon]) {
            loop {
                let declarator = self.parse_declarator(None)?;
                let initializer = if self.matches(&[TokenKind::Assign]) {
                    self.advance(); // consume '='
                    Some(self.parse_initializer()?)
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
        }

        let semicolon_token = self.expect(TokenKind::Semicolon)?;

        let end_span = semicolon_token.location.end;

        let span = SourceSpan::new(start_span, end_span);

        // Track typedef names for disambiguation
        for specifier in &specifiers {
            if specifier.storage_class == Some(StorageClass::Typedef) {
                for init_declarator in &init_declarators {
                    if let Declarator::Identifier(name, _, _) = &init_declarator.declarator {
                        self.typedef_names.insert(*name);
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
        Ok(node)
    }

    /// Parse declaration specifiers
    fn parse_declaration_specifiers(&mut self) -> Result<Vec<DeclSpecifier>, ParseError> {
        let mut specifiers = Vec::new();

        loop {
            let token = match self.current_token() {
                Some(t) => t,
                None => break,
            };

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
                    while let Some(token) = self.current_token() {
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
                    while let Some(token) = self.current_token() {
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
                }

                TokenKind::Identifier(symbol) => {
                    if self.is_type_name(symbol) {
                        let type_specifier = self.parse_type_specifier()?;
                        specifiers.push(DeclSpecifier {
                            storage_class: None,
                            type_qualifiers: TypeQualifiers::empty(),
                            function_specifiers: FunctionSpecifiers::empty(),
                            alignment_specifier: None,
                            type_specifier,
                        });
                    } else {
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

                _ => break,
            }
        }

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
        let token = self
            .current_token()
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
                Ok(TypeSpecifier::Long)
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
                self.parse_struct_or_union_specifier(false)
            }
            TokenKind::Union => {
                self.advance();
                self.parse_struct_or_union_specifier(true)
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

    /// Parse struct or union specifier
    fn parse_struct_or_union_specifier(
        &mut self,
        is_union: bool,
    ) -> Result<TypeSpecifier, ParseError> {
        let tag = if let Some(token) = self.current_token() {
            if let TokenKind::Identifier(symbol) = token.kind {
                self.advance();
                Some(symbol)
            } else {
                None
            }
        } else {
            None
        };

        let definition = if self.matches(&[TokenKind::LeftBrace]) {
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
        let tag = if let Some(token) = self.current_token() {
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
        let specifiers = self.parse_declaration_specifiers()?;
        let mut declarators = Vec::new();

        while !self.matches(&[TokenKind::Semicolon]) {
            // Check for anonymous struct/union (C11)
            if self.matches(&[TokenKind::Struct, TokenKind::Union]) {
                // Anonymous struct/union member
                let is_union = self.matches(&[TokenKind::Union]);
                self.advance(); // consume struct/union
                self.expect(TokenKind::LeftBrace)?;
                let members = self.parse_struct_declaration_list()?;
                self.expect(TokenKind::RightBrace)?;
                // Create a synthetic declarator for anonymous member
                declarators.push(InitDeclarator {
                    declarator: Declarator::AnonymousRecord(is_union, members),
                    initializer: None,
                });
            } else {
                let declarator = self.parse_declarator(None)?;
                declarators.push(InitDeclarator {
                    declarator,
                    initializer: None, // Struct members can't have initializers
                });
            }

            if !self.matches(&[TokenKind::Comma]) {
                break;
            }
            self.advance(); // consume comma
        }

        self.expect(TokenKind::Semicolon)?;

        Ok(DeclarationData {
            specifiers,
            init_declarators: declarators,
        })
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
            .current_token()
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

        let span = SourceSpan::new(
            token.location.start,
            self.current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
        );

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
        let specifiers = self.parse_declaration_specifiers()?;

        // Parse abstract declarator (optional)
        let declarator = if self.is_abstract_declarator_start() {
            Some(self.parse_abstract_declarator()?)
        } else {
            None
        };

        // TODO: Build the type from specifiers and declarator
        // For now, return a placeholder type
        Ok(self.ast.push_type(Type {
            kind: TypeKind::Void,
            qualifiers: TypeQualifiers::empty(),
            size: None,
            alignment: None,
        }))
    }

    /// Parse initializer
    fn parse_initializer(&mut self) -> Result<Initializer, ParseError> {
        if self.matches(&[TokenKind::LeftBrace]) {
            // Compound initializer
            self.advance(); // consume '{'
            let mut initializers = Vec::new();

            while !self.matches(&[TokenKind::RightBrace]) {
                let designated_init = self.parse_designated_initializer()?;
                initializers.push(designated_init);

                if !self.matches(&[TokenKind::Comma]) {
                    break;
                }
                self.advance(); // consume comma
            }

            self.expect(TokenKind::RightBrace)?;
            Ok(Initializer::List(initializers))
        } else {
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
                    .current_token()
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
        let mut current_qualifiers = TypeQualifiers::empty();

        // Parse leading pointers and their qualifiers
        while self.matches(&[TokenKind::Star]) {
            self.advance(); // Consume '*'
            current_qualifiers = self.parse_type_qualifiers()?;
            declarator_chain.push(DeclaratorComponent::Pointer(current_qualifiers));
            current_qualifiers = TypeQualifiers::empty(); // Reset for next component
        }

        // Parse direct declarator (identifier or parenthesized declarator)
        let base_declarator = if self.matches(&[TokenKind::LeftParen]) {
            self.advance(); // Consume '('
            let inner_declarator = self.parse_declarator(None)?;
            self.expect(TokenKind::RightParen)?; // Consume ')'
            inner_declarator
        } else if let Some(ident_symbol) = initial_declarator {
            Declarator::Identifier(ident_symbol, TypeQualifiers::empty(), None)
        } else if let Some(token) = self.current_token() {
            if let TokenKind::Identifier(symbol) = token.kind {
                self.advance(); // Consume identifier
                Declarator::Identifier(symbol, TypeQualifiers::empty(), None)
            } else {
                return Err(ParseError::UnexpectedToken {
                    expected: vec![
                        TokenKind::Star,
                        TokenKind::LeftParen,
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
        while let Some(token) = self.current_token() {
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
        if self.matches(&[TokenKind::Static]) {
            // VLA specifier: static [expression]
            self.advance();
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(expr_node) => Ok(ArraySize::VlaSpecifier(Some(expr_node))),
                _ => Err(ParseError::SyntaxError {
                    message: "Expected expression after 'static' in VLA specifier".to_string(),
                    location: self.current_token().unwrap().location,
                }),
            }
        } else if self.matches(&[TokenKind::Star]) {
            self.advance();
            Ok(ArraySize::Star)
        } else if self.matches(&[TokenKind::RightBracket]) {
            // Empty []
            Ok(ArraySize::Incomplete)
        } else {
            // Assume it's an expression for the size
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(expr_node) => Ok(ArraySize::Expression(expr_node)),
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

                    let specifiers = self.parse_declaration_specifiers()?;
                    let declarator = if !self.matches(&[TokenKind::Comma])
                        && !self.matches(&[TokenKind::RightParen])
                    {
                        Some(self.parse_declarator(None)?)
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
            .current_token()
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Expected statement".to_string(),
                location: SourceSpan::empty(),
            })?;

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::LeftBrace)?;

        let mut block_items = Vec::new();

        while !self.matches(&[TokenKind::RightBrace]) {
            if self.is_declaration_start() {
                let declaration = self.parse_declaration()?;
                block_items.push(declaration);
            } else {
                let statement = self.parse_statement()?;
                block_items.push(statement);
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
        if let Some(token) = self.current_token() {
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
                    self.is_type_name(symbol)
                }
                _ => false,
            }
        } else {
            false
        }
    }

    /// Parse if statement
    fn parse_if_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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

        let body = self.parse_statement()?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let while_stmt = WhileStmt { condition, body };

        let node = self
            .ast
            .push_node(Node::new(NodeKind::While(while_stmt), span));
        Ok(node)
    }

    /// Parse do-while statement
    fn parse_do_while_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::For)?;
        self.expect(TokenKind::LeftParen)?;

        // Parse initialization
        let init = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else if self.is_declaration_start() {
            Some(self.parse_declaration()?)
        } else {
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

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Goto)?;

        let token = self
            .current_token()
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
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Goto(label), span));
        Ok(node)
    }

    /// Parse continue statement
    fn parse_continue_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Continue)?;
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Continue, span));
        Ok(node)
    }

    /// Parse break statement
    fn parse_break_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Break)?;
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Break, span));
        Ok(node)
    }

    /// Parse return statement
    fn parse_return_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Return)?;

        let value = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else {
            let expr_result = self.parse_expression(BindingPower::MIN)?;
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

        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(NodeKind::Return(value), span));
        Ok(node)
    }

    /// Parse empty statement
    fn parse_empty_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::EmptyStatement, span));
        Ok(node)
    }

    /// Parse case statement (including GNU case ranges)
    fn parse_case_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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
                        message: "Expected constant expression after '...' in case range".to_string(),
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

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Default)?;
        self.expect(TokenKind::Colon)?;

        let statement = self.parse_statement()?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::Default(statement), span));
        Ok(node)
    }

    /// Parse expression statement
    fn parse_expression_statement(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));

        let expression = if self.matches(&[TokenKind::Semicolon]) {
            None
        } else {
            let expr_result = self.parse_expression(BindingPower::MIN)?;
            match expr_result {
                ParseExprOutput::Expression(node) => Some(node),
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in expression statement".to_string(),
                        location: self.current_token().unwrap().location,
                    });
                }
            }
        };

        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::ExpressionStatement(expression), span));
        Ok(node)
    }

    /// Parse function definition
    pub fn parse_function_definition(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));

        let mut top_level_declarations = Vec::new();
        let mut iteration_count = 0;
        const MAX_ITERATIONS: usize = 10000; // Prevent infinite loops

        while let Some(token) = self.current_token() {
            if token.kind == TokenKind::EndOfFile {
                break;
            }

            // Prevent infinite loops by limiting iterations
            iteration_count += 1;
            if iteration_count > MAX_ITERATIONS {
                return Err(ParseError::SyntaxError {
                    message: "Parser exceeded maximum iteration limit - possible infinite loop"
                        .to_string(),
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

            // Ensure we made progress - if we didn't advance, force advance to prevent infinite loop
            if self.current_idx == initial_idx {
                // Skip the current token to make progress
                self.advance();
            }
        }

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self.ast.push_node(Node::new(
            NodeKind::TranslationUnit(top_level_declarations),
            span,
        ));
        Ok(node)
    }

    /// Check if current tokens indicate start of a function definition
    fn is_function_definition_start(&self) -> bool {
        // Function definitions start with declaration specifiers like declarations,
        // but we distinguish them during parsing by trying declaration first
        false // Always try declaration first, then function definition if failed
    }

    /// Parse _Generic selection (C11)
    pub fn parse_generic_selection(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
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

        self.expect(TokenKind::RightParen)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        self.expect(TokenKind::LeftParen)?;
        let type_ref = self.parse_type_name()?;
        self.expect(TokenKind::RightParen)?;

        let initializer = self.parse_initializer()?;

        let span = SourceSpan {
            start: SourceLoc(0), // Would need to track start properly
            end: self
                .current_token()
                .map(|t| t.location.end)
                .unwrap_or(SourceLoc(0)),
        };

        let initializer = self.ast.push_initializer(initializer);
        let node = self.ast.push_node(Node {
            kind: NodeKind::CompoundLiteral(type_ref, initializer),
            span,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        });
        Ok(node)
    }

    /// Parse static assert (C11)
    pub fn parse_static_assert(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::StaticAssert)?;
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
            .current_token()
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
        self.expect(TokenKind::Semicolon)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

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
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Sizeof)?;

        let node = if self.matches(&[TokenKind::LeftParen]) {
            self.advance(); // consume '('
            // Check if it's a type name or expression
            if self.is_type_name_start() {
                let type_ref = self.parse_type_name()?;
                self.expect(TokenKind::RightParen)?;

                let end_span = self
                    .current_token()
                    .map(|t| t.location.end)
                    .unwrap_or(SourceLoc(0));
                let span = SourceSpan::new(start_span, end_span);

                self.ast
                    .push_node(Node::new(NodeKind::SizeOfType(type_ref), span))
            } else {
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
                self.expect(TokenKind::RightParen)?;

                let end_span = self
                    .current_token()
                    .map(|t| t.location.end)
                    .unwrap_or(SourceLoc(0));
                let span = SourceSpan::new(start_span, end_span);

                self.ast
                    .push_node(Node::new(NodeKind::SizeOfExpr(expr), span))
            }
        } else {
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

            self.ast
                .push_node(Node::new(NodeKind::SizeOfExpr(expr), span))
        };

        Ok(node)
    }

    /// Parse _Alignof (C11)
    pub fn parse_alignof(&mut self) -> Result<NodeRef, ParseError> {
        let start_span = self
            .current_token()
            .map(|t| t.location.start)
            .unwrap_or(SourceLoc(0));
        self.expect(TokenKind::Alignof)?;
        self.expect(TokenKind::LeftParen)?;

        let type_ref = self.parse_type_name()?;
        self.expect(TokenKind::RightParen)?;

        let end_span = self
            .current_token()
            .map(|t| t.location.end)
            .unwrap_or(SourceLoc(0));

        let span = SourceSpan::new(start_span, end_span);

        let node = self
            .ast
            .push_node(Node::new(NodeKind::AlignOf(type_ref), span));
        Ok(node)
    }

    /// Check if current token starts a type name
    fn is_type_name_start(&self) -> bool {
        if let Some(token) = self.current_token() {
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
                | TokenKind::Enum
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic
                | TokenKind::Identifier(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    /// Check if current token starts an abstract declarator
    fn is_abstract_declarator_start(&self) -> bool {
        if let Some(token) = self.current_token() {
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

    /// Parse abstract declarator (for type names without identifiers)
    fn parse_abstract_declarator(&mut self) -> Result<Declarator, ParseError> {
        let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
        let mut current_qualifiers = TypeQualifiers::empty();

        // Parse leading pointers and their qualifiers
        while self.matches(&[TokenKind::Star]) {
            self.advance(); // Consume '*'
            current_qualifiers = self.parse_type_qualifiers()?;
            declarator_chain.push(DeclaratorComponent::Pointer(current_qualifiers));
            current_qualifiers = TypeQualifiers::empty(); // Reset for next component
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
        // Check if the symbol is in our typedef names set
        self.typedef_names.contains(&symbol) ||
        // Also check built-in types that might be typedef'd
        matches!(symbol.as_str(), "size_t" | "ptrdiff_t" | "intmax_t" | "uintmax_t" |
                 "intptr_t" | "uintptr_t" | "int8_t" | "int16_t" | "int32_t" | "int64_t" |
                 "uint8_t" | "uint16_t" | "uint32_t" | "uint64_t" | "int_least8_t" |
                 "int_least16_t" | "int_least32_t" | "int_least64_t" | "uint_least8_t" |
                 "uint_least16_t" | "uint_least32_t" | "uint_least64_t" | "int_fast8_t" |
                 "int_fast16_t" | "int_fast32_t" | "int_fast64_t" | "uint_fast8_t" |
                 "uint_fast16_t" | "uint_fast32_t" | "uint_fast64_t")
    }
}
