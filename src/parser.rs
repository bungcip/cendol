//! Parser module for C11 compiler
//!
//! This module provides the main parser coordination, public API, and state management.
//! It orchestrates the parsing process by delegating to specialized sub-modules for
//! different language constructs.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, ParseError};
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use std::collections::HashSet;
use symbol_table::GlobalSymbol as Symbol;

pub mod declaration_core;
pub mod declarations;
pub mod declarator;
pub mod enum_parsing;
pub mod expressions;
pub mod statements;
pub mod struct_parsing;
pub mod type_specifiers;
pub mod utils;

// Re-export commonly used types
pub use expressions::{Associativity, BindingPower, PrattParser};

use expressions::parse_expression;
use utils::unwrap_expr_result;

/// Type context for tracking typedef names and other type-related state
#[derive(Debug)]
pub struct TypeContext {
    /// Set of typedef names for disambiguation
    typedef_names: HashSet<Symbol>,
}

impl Default for TypeContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeContext {
    /// Create a new type context with builtin typedefs
    pub fn new() -> Self {
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

        TypeContext { typedef_names }
    }

    /// Check if a symbol is a typedef name
    pub fn is_type_name(&self, symbol: Symbol) -> bool {
        let result = self.typedef_names.contains(&symbol);
        debug!("is_type_name({:?}) = {}", symbol, result);
        result
    }

    /// Add a typedef name
    pub fn add_typedef(&mut self, symbol: Symbol) {
        self.typedef_names.insert(symbol);
    }
}

/// Result of parsing an expression
#[derive(Debug)]
pub enum ParseExprOutput {
    Expression(NodeRef),
    Declaration(NodeRef), // For cases where we parse a declaration instead
}

/// Error recovery point for backtracking
#[derive(Debug)]
pub struct ErrorRecoveryPoint {
    pub token_index: usize,
    pub context: String,
}

#[derive(Debug, Clone)]
pub struct ParserState {
    current_idx: usize,
    diag_len: usize,
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

    // Type context for typedef tracking
    type_context: TypeContext,
}

impl<'arena, 'src> Parser<'arena, 'src> {
    /// Create a new parser
    pub fn new(tokens: &'src [Token], ast: &'arena mut Ast, diag: &'src mut DiagnosticEngine) -> Self {
        Parser {
            tokens,
            current_idx: 0,
            ast,
            diag,
            in_function_body: false,
            in_struct_declaration: false,
            in_enum_declaration: false,
            error_recovery_points: Vec::new(),
            type_context: TypeContext::new(),
        }
    }

    /// Get the current token (returns None if at end of input)
    fn try_current_token(&self) -> Option<Token> {
        self.tokens.get(self.current_idx).cloned()
    }

    /// Get the current token (returns error if at end of input)
    fn current_token(&self) -> Result<Token, ParseError> {
        self.try_current_token().ok_or_else(|| ParseError::SyntaxError {
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

    /// Accept a specific token kind if found, consume it and return it, otherwise nothing happens
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
        self.current_token_kind().map(|k| kinds.contains(&k)).unwrap_or(false)
    }

    /// Check if current token matches the given kind
    fn is_token(&self, kind: TokenKind) -> bool {
        self.current_token_kind() == Some(kind)
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
    fn parse_c11_float_literal(&self, text: Symbol, location: SourceSpan) -> Result<f64, ParseError> {
        let text_str = text.as_str();

        // C11 floating-point literal format:
        // [digits][.digits][e|E[+|-]digits][f|F|l|L]
        // or [digits][e|E[+|-]digits][f|F|l|L]
        // or 0[xX][hexdigits][.hexdigits][p|P[+|-]digits][f|F|l|L]

        // Strip suffix (f, F, l, L) for parsing
        let text_without_suffix =
            if text_str.ends_with('f') || text_str.ends_with('F') || text_str.ends_with('l') || text_str.ends_with('L')
            {
                &text_str[..text_str.len() - 1]
            } else {
                text_str
            };

        // Handle hexadecimal floating-point literals (C99/C11)
        if text_str.starts_with("0x") || text_str.starts_with("0X") {
            self.parse_hex_float_literal(text_without_suffix, location)
        } else {
            // Use Rust's built-in parsing for decimal floats
            match text_without_suffix.parse::<f64>() {
                Ok(val) => Ok(val),
                Err(_) => Err(ParseError::SyntaxError {
                    message: format!("Invalid floating-point constant: {}", text_str),
                    location,
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
                message: format!("Invalid exponent '{}' in hexadecimal float literal", exp_str),
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
        min_binding_power: expressions::BindingPower,
    ) -> Result<ParseExprOutput, ParseError> {
        parse_expression(self, min_binding_power)
    }

    /// Parse a declaration
    pub fn parse_declaration(&mut self) -> Result<NodeRef, ParseError> {
        declarations::parse_declaration(self)
    }

    /// Parse a statement
    pub fn parse_statement(&mut self) -> Result<NodeRef, ParseError> {
        statements::parse_statement(self)
    }

    /// Parse function definition
    pub fn parse_function_definition(&mut self) -> Result<NodeRef, ParseError> {
        declarations::parse_function_definition(self)
    }

    /// Parse translation unit (top level)
    pub fn parse_translation_unit(&mut self) -> Result<NodeRef, ParseError> {
        declarations::parse_translation_unit(self)
    }

    /// Parse _Generic selection (C11)
    pub fn parse_generic_selection(&mut self) -> Result<NodeRef, ParseError> {
        expressions::parse_generic_selection(self)
    }

    /// Parse compound literal (C99)
    pub fn parse_compound_literal(&mut self) -> Result<NodeRef, ParseError> {
        expressions::parse_compound_literal(self)
    }

    /// Parse static assert (C11)
    pub fn parse_static_assert(&mut self, start_token: Token) -> Result<NodeRef, ParseError> {
        declarations::parse_static_assert(self, start_token)
    }

    /// Parse sizeof expression or type
    pub fn parse_sizeof(&mut self) -> Result<NodeRef, ParseError> {
        expressions::parse_sizeof(self)
    }

    /// Parse _Alignof (C11)
    pub fn parse_alignof(&mut self) -> Result<NodeRef, ParseError> {
        expressions::parse_alignof(self)
    }

    /// Check if current token starts a type name
    fn is_type_name_start(&self) -> bool {
        declarations::is_type_name_start(self)
    }

    /// Check if current token starts an abstract declarator
    fn is_abstract_declarator_start(&self) -> bool {
        declarator::is_abstract_declarator_start(self)
    }

    /// Extract the declared name from a declarator, if any
    fn get_declarator_name(&self, declarator: &crate::ast::Declarator) -> Option<Symbol> {
        declarator::get_declarator_name(declarator)
    }

    /// Disambiguates between a type name and an identifier in ambiguous contexts.
    /// This is crucial for parsing C's "declaration-specifier-list" vs "expression" ambiguity.
    fn is_type_name(&self, symbol: Symbol) -> bool {
        self.type_context.is_type_name(symbol)
    }

    /// Check if a cast expression starts at the current position
    /// This is called after consuming an opening parenthesis
    fn is_cast_expression_start(&self) -> bool {
        expressions::is_cast_expression_start(self)
    }

    // /// Helper for more complex cast expression detection
    // fn is_cast_expression_start_advanced(&self) -> bool {
    //     expressions::is_cast_expression_start_advanced(self)
    // }

    /// Parse cast expression given the already parsed type and right paren token
    fn parse_cast_expression_from_type_and_paren(
        &mut self,
        type_ref: TypeRef,
        right_paren_token: Token,
    ) -> Result<NodeRef, ParseError> {
        expressions::parse_cast_expression_from_type_and_paren(self, type_ref, right_paren_token)
    }

    /// Parse compound literal given the type and start location
    fn parse_compound_literal_from_type_and_start(
        &mut self,
        type_ref: TypeRef,
        start_loc: SourceLoc,
    ) -> Result<NodeRef, ParseError> {
        expressions::parse_compound_literal_from_type_and_start(self, type_ref, start_loc)
    }

    /// Add a typedef name to the type context
    pub fn add_typedef(&mut self, symbol: Symbol) {
        debug!("add_typedef: adding {:?} to typedef_names", symbol);
        self.type_context.add_typedef(symbol);
    }

    fn save_state(&self) -> ParserState {
        ParserState {
            current_idx: self.current_idx,
            diag_len: self.diag.diagnostics.len(),
        }
    }

    fn restore_state(&mut self, state: ParserState) {
        self.current_idx = state.current_idx;
        self.diag.diagnostics.truncate(state.diag_len);
    }

    pub fn start_transaction(&mut self) -> utils::ParserTransaction<'_, 'arena, 'src> {
        utils::ParserTransaction::new(self)
    }
}

mod tests_parser;
