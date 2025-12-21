use crate::pp::{PPToken, PPTokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use symbol_table::GlobalSymbol as Symbol;

use hashbrown::HashMap;
use std::sync::OnceLock;

// Re-export DiagnosticEngine from diagnostic module for convenience
pub use crate::diagnostic::DiagnosticEngine;

/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    // === LITERALS ===
    IntegerConstant(i64),  // Parsed integer literal value
    FloatConstant(f64),    // Parsed float literal value
    CharacterConstant(u8), // Byte value of character constant
    StringLiteral(Symbol), // Interned string literal

    // === IDENTIFIERS ===
    Identifier(Symbol), // Interned identifier

    // === KEYWORDS ===
    // Storage class specifiers
    Auto,
    Extern,
    Register,
    Static,
    ThreadLocal,

    // Type qualifiers
    Const,
    Restrict,
    Volatile,
    Atomic,

    // Type specifiers
    Bool,
    Char,
    Double,
    Float,
    Int,
    Long,
    Short,
    Signed,
    Unsigned,
    Void,
    Complex,

    // Complex type specifiers
    Struct,
    Union,
    Enum,

    // Control flow
    Break,
    Case,
    Continue,
    Default,
    Do,
    Else,
    For,
    Goto,
    If,
    Return,
    Switch,
    While,

    // Other keywords
    Alignas,
    Alignof,
    Generic,
    Inline,
    Noreturn,
    Pragma,
    Sizeof,
    StaticAssert,
    Typedef,
    Attribute,

    // === OPERATORS ===
    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Increment,
    Decrement,

    // Bitwise operators
    And,
    Or,
    Xor,
    Not,
    Tilde,
    LeftShift,
    RightShift,

    // Comparison operators
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,

    // Assignment operators
    Assign,
    PlusAssign,
    MinusAssign,
    StarAssign,
    DivAssign,
    ModAssign,
    AndAssign,
    OrAssign,
    XorAssign,
    LeftShiftAssign,
    RightShiftAssign,

    // Logical operators
    LogicAnd,
    LogicOr,

    // Member access
    Arrow,
    Dot,

    // Ternary operator
    Question,
    Colon,

    // === PUNCTUATION ===
    Comma,
    Semicolon,
    Ellipsis,

    // Brackets and parentheses
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,

    // === SPECIAL TOKENS ===
    EndOfFile,
    Unknown,
}

impl TokenKind {
    /// Check if the token is a storage class specifier
    pub fn is_storage_class_specifier(&self) -> bool {
        matches!(
            self,
            TokenKind::Typedef
                | TokenKind::Extern
                | TokenKind::Static
                | TokenKind::ThreadLocal
                | TokenKind::Auto
                | TokenKind::Register
        )
    }

    /// Check if the token is a type specifier
    pub fn is_type_specifier(&self) -> bool {
        matches!(
            self,
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
        )
    }

    /// Check if the token is a type qualifier
    pub fn is_type_qualifier(&self) -> bool {
        matches!(self, TokenKind::Const | TokenKind::Restrict | TokenKind::Volatile)
    }

    /// Check if the token is a function specifier
    pub fn is_function_specifier(&self) -> bool {
        matches!(self, TokenKind::Inline | TokenKind::Noreturn)
    }

    /// Check if the token is an alignment specifier
    pub fn is_alignment_specifier(&self) -> bool {
        matches!(self, TokenKind::Alignas)
    }

    /// Check if the token can start a declaration specifier
    pub fn is_declaration_specifier_start(&self) -> bool {
        self.is_storage_class_specifier()
            || self.is_type_specifier()
            || self.is_type_qualifier()
            || self.is_function_specifier()
            || self.is_alignment_specifier()
            || matches!(self, TokenKind::Attribute)
    }

    /// Check if the token can start a declaration (including typedefs)
    pub fn is_declaration_start(&self, is_typedef: bool) -> bool {
        if self.is_declaration_specifier_start() {
            return true;
        }

        if let TokenKind::Identifier(_) = self {
            return is_typedef;
        }

        false
    }
}

/// Token with source location for the parser
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub location: SourceSpan,
}

/// Static keyword lookup table for O(1) keyword recognition
static KEYWORDS: OnceLock<HashMap<&'static str, TokenKind>> = OnceLock::new();

/// Static punctuation mapping for systematic token classification
static PUNCTUATION_MAP: OnceLock<HashMap<PPTokenKind, TokenKind>> = OnceLock::new();

/// Initialize the keyword map
fn init_keywords() -> HashMap<&'static str, TokenKind> {
    let mut map = HashMap::new();

    // C11 keywords
    map.insert("auto", TokenKind::Auto);
    map.insert("break", TokenKind::Break);
    map.insert("case", TokenKind::Case);
    map.insert("char", TokenKind::Char);
    map.insert("const", TokenKind::Const);
    map.insert("continue", TokenKind::Continue);
    map.insert("default", TokenKind::Default);
    map.insert("do", TokenKind::Do);
    map.insert("double", TokenKind::Double);
    map.insert("else", TokenKind::Else);
    map.insert("enum", TokenKind::Enum);
    map.insert("extern", TokenKind::Extern);
    map.insert("float", TokenKind::Float);
    map.insert("for", TokenKind::For);
    map.insert("goto", TokenKind::Goto);
    map.insert("if", TokenKind::If);
    map.insert("inline", TokenKind::Inline);
    map.insert("int", TokenKind::Int);
    map.insert("long", TokenKind::Long);
    map.insert("register", TokenKind::Register);
    map.insert("restrict", TokenKind::Restrict);
    map.insert("return", TokenKind::Return);
    map.insert("short", TokenKind::Short);
    map.insert("signed", TokenKind::Signed);
    map.insert("sizeof", TokenKind::Sizeof);
    map.insert("static", TokenKind::Static);
    map.insert("struct", TokenKind::Struct);
    map.insert("switch", TokenKind::Switch);
    map.insert("typedef", TokenKind::Typedef);
    map.insert("union", TokenKind::Union);
    map.insert("unsigned", TokenKind::Unsigned);
    map.insert("void", TokenKind::Void);
    map.insert("volatile", TokenKind::Volatile);
    map.insert("while", TokenKind::While);

    // C11 specific keywords
    map.insert("_Alignas", TokenKind::Alignas);
    map.insert("_Alignof", TokenKind::Alignof);
    map.insert("_Atomic", TokenKind::Atomic);
    map.insert("_Bool", TokenKind::Bool);
    map.insert("_Complex", TokenKind::Complex);
    map.insert("_Generic", TokenKind::Generic);
    map.insert("_Noreturn", TokenKind::Noreturn);
    map.insert("_Pragma", TokenKind::Pragma);
    map.insert("_Static_assert", TokenKind::StaticAssert);
    map.insert("_Thread_local", TokenKind::ThreadLocal);

    // GCC extensions
    map.insert("__attribute__", TokenKind::Attribute);
    map.insert("__attribute", TokenKind::Attribute);

    map
}

/// Initialize the punctuation mapping
fn init_punctuation_map() -> HashMap<PPTokenKind, TokenKind> {
    let mut map = HashMap::new();

    // Arithmetic operators
    map.insert(PPTokenKind::Plus, TokenKind::Plus);
    map.insert(PPTokenKind::Minus, TokenKind::Minus);
    map.insert(PPTokenKind::Star, TokenKind::Star);
    map.insert(PPTokenKind::Slash, TokenKind::Slash);
    map.insert(PPTokenKind::Percent, TokenKind::Percent);
    map.insert(PPTokenKind::Increment, TokenKind::Increment);
    map.insert(PPTokenKind::Decrement, TokenKind::Decrement);

    // Bitwise operators
    map.insert(PPTokenKind::And, TokenKind::And);
    map.insert(PPTokenKind::Or, TokenKind::Or);
    map.insert(PPTokenKind::Xor, TokenKind::Xor);
    map.insert(PPTokenKind::Not, TokenKind::Not);
    map.insert(PPTokenKind::Tilde, TokenKind::Tilde);
    map.insert(PPTokenKind::LeftShift, TokenKind::LeftShift);
    map.insert(PPTokenKind::RightShift, TokenKind::RightShift);

    // Comparison operators
    map.insert(PPTokenKind::Less, TokenKind::Less);
    map.insert(PPTokenKind::Greater, TokenKind::Greater);
    map.insert(PPTokenKind::LessEqual, TokenKind::LessEqual);
    map.insert(PPTokenKind::GreaterEqual, TokenKind::GreaterEqual);
    map.insert(PPTokenKind::Equal, TokenKind::Equal);
    map.insert(PPTokenKind::NotEqual, TokenKind::NotEqual);

    // Assignment operators
    map.insert(PPTokenKind::Assign, TokenKind::Assign);
    map.insert(PPTokenKind::PlusAssign, TokenKind::PlusAssign);
    map.insert(PPTokenKind::MinusAssign, TokenKind::MinusAssign);
    map.insert(PPTokenKind::StarAssign, TokenKind::StarAssign);
    map.insert(PPTokenKind::DivAssign, TokenKind::DivAssign);
    map.insert(PPTokenKind::ModAssign, TokenKind::ModAssign);
    map.insert(PPTokenKind::AndAssign, TokenKind::AndAssign);
    map.insert(PPTokenKind::OrAssign, TokenKind::OrAssign);
    map.insert(PPTokenKind::XorAssign, TokenKind::XorAssign);
    map.insert(PPTokenKind::LeftShiftAssign, TokenKind::LeftShiftAssign);
    map.insert(PPTokenKind::RightShiftAssign, TokenKind::RightShiftAssign);

    // Logical operators
    map.insert(PPTokenKind::LogicAnd, TokenKind::LogicAnd);
    map.insert(PPTokenKind::LogicOr, TokenKind::LogicOr);

    // Member access
    map.insert(PPTokenKind::Arrow, TokenKind::Arrow);
    map.insert(PPTokenKind::Dot, TokenKind::Dot);

    // Ternary operator
    map.insert(PPTokenKind::Question, TokenKind::Question);
    map.insert(PPTokenKind::Colon, TokenKind::Colon);

    // Punctuation
    map.insert(PPTokenKind::Comma, TokenKind::Comma);
    map.insert(PPTokenKind::Semicolon, TokenKind::Semicolon);
    map.insert(PPTokenKind::Ellipsis, TokenKind::Ellipsis);

    // Brackets and parentheses
    map.insert(PPTokenKind::LeftParen, TokenKind::LeftParen);
    map.insert(PPTokenKind::RightParen, TokenKind::RightParen);
    map.insert(PPTokenKind::LeftBracket, TokenKind::LeftBracket);
    map.insert(PPTokenKind::RightBracket, TokenKind::RightBracket);
    map.insert(PPTokenKind::LeftBrace, TokenKind::LeftBrace);
    map.insert(PPTokenKind::RightBrace, TokenKind::RightBrace);

    // Special tokens that map to Unknown
    map.insert(PPTokenKind::Hash, TokenKind::Unknown);
    map.insert(PPTokenKind::HashHash, TokenKind::Unknown);

    map
}

/// Check if a symbol represents a C11 keyword
pub fn is_keyword(symbol: Symbol) -> Option<TokenKind> {
    KEYWORDS.get_or_init(init_keywords).get(symbol.as_str()).copied()
}

/// Lexer state machine
pub struct Lexer<'src> {
    // Current position in token stream
    tokens: &'src [PPToken],
    current_index: usize,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer with the given preprocessor token stream
    pub fn new(tokens: &'src [PPToken]) -> Self {
        Lexer {
            tokens,
            current_index: 0,
        }
    }

    /// Parse C11 integer literal syntax
    fn parse_c11_integer_literal(&self, text: Symbol) -> Result<i64, ()> {
        let text_str = text.as_str();

        // Extract the numeric part and determine base
        let (digits, base) = Self::extract_digits_and_base(text_str)?;

        // Parse the number
        Self::parse_integer_value(digits, base)
    }

    /// Extract digits and determine base from integer literal text
    fn extract_digits_and_base(text: &str) -> Result<(&str, u32), ()> {
        // Remove suffix to get just the numeric part
        let digits_part = Self::strip_integer_suffix(text);

        // Determine base
        if digits_part.starts_with("0x") || digits_part.starts_with("0X") {
            Ok((&digits_part[2..], 16))
        } else if digits_part.starts_with('0') && digits_part.len() > 1 {
            Ok((&digits_part[1..], 8))
        } else {
            Ok((digits_part, 10))
        }
    }

    /// Strip integer literal suffix (u, l, ll, ul, ull, etc.)
    fn strip_integer_suffix(text: &str) -> &str {
        // Performance: Use case-insensitive comparison to avoid heap allocation from `to_lowercase()`.
        // C11 integer suffixes are case-insensitive (e.g., U, l, LL).
        // Check for longest suffixes first for correctness.
        let len = text.len();

        if len >= 3 {
            let suffix = &text[len - 3..];
            if suffix.eq_ignore_ascii_case("ull") || suffix.eq_ignore_ascii_case("llu") {
                return &text[..len - 3];
            }
        }

        if len >= 2 {
            let suffix = &text[len - 2..];
            if suffix.eq_ignore_ascii_case("ul")
                || suffix.eq_ignore_ascii_case("lu")
                || suffix.eq_ignore_ascii_case("ll")
            {
                return &text[..len - 2];
            }
        }

        if len >= 1 {
            let suffix = &text[len - 1..];
            if suffix.eq_ignore_ascii_case("u") || suffix.eq_ignore_ascii_case("l") {
                return &text[..len - 1];
            }
        }

        text
    }

    /// Parse integer value from digits and base
    fn parse_integer_value(digits: &str, base: u32) -> Result<i64, ()> {
        let value = match base {
            16 => u64::from_str_radix(digits, 16),
            8 => u64::from_str_radix(digits, 8),
            10 => digits.parse::<u64>(),
            _ => return Err(()),
        };

        value.map(|v| v as i64).map_err(|_| ())
    }

    /// Get the next token from the stream
    pub fn next_token(&mut self) -> Option<Token> {
        if self.current_index >= self.tokens.len() {
            return None;
        }

        let pptoken = &self.tokens[self.current_index];
        self.current_index += 1;

        let token_kind = self.classify_token(pptoken);
        let location = SourceSpan {
            start: pptoken.location,
            end: SourceLoc::new(
                pptoken.location.source_id(),
                pptoken.location.offset() + pptoken.length as u32,
            ),
        };

        let token = Token {
            kind: token_kind,
            location,
        };

        Some(token)
    }

    /// Classify a preprocessor token into a lexical token
    fn classify_token(&self, pptoken: &PPToken) -> TokenKind {
        match pptoken.kind {
            PPTokenKind::Identifier(symbol) => {
                // Check if it's a keyword
                is_keyword(symbol).unwrap_or(TokenKind::Identifier(symbol))
            }
            PPTokenKind::StringLiteral(symbol) => TokenKind::StringLiteral(symbol),
            PPTokenKind::CharLiteral(codepoint, _) => TokenKind::CharacterConstant(codepoint),
            PPTokenKind::Number(value) => {
                // Try to parse as integer first, then float, then unknown
                if let Ok(int_val) = self.parse_c11_integer_literal(value) {
                    TokenKind::IntegerConstant(int_val)
                } else if let Ok(float_val) = self.parse_c11_float_literal(value) {
                    TokenKind::FloatConstant(float_val)
                } else {
                    TokenKind::Unknown // Could not parse as integer or float
                }
            }
            PPTokenKind::Eof => TokenKind::EndOfFile,
            PPTokenKind::Eod => TokenKind::Unknown,
            // Handle punctuation tokens systematically
            pptoken_kind => PUNCTUATION_MAP
                .get_or_init(init_punctuation_map)
                .get(&pptoken_kind)
                .copied()
                .unwrap_or(TokenKind::Unknown),
        }
    }

    /// Peek at the next token without consuming it
    pub fn peek_token(&self) -> Option<TokenKind> {
        if self.current_index >= self.tokens.len() {
            return None;
        }

        let pptoken = &self.tokens[self.current_index];
        Some(match self.classify_token(pptoken) {
            TokenKind::EndOfFile => TokenKind::EndOfFile,
            kind => kind,
        })
    }

    /// Get all tokens from the stream
    pub fn tokenize_all(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        let mut current_token_iter = self.tokens.iter().peekable();

        while let Some(pptoken) = current_token_iter.next() {
            // next_token logic inlined and adapted
            let mut token = Token {
                kind: self.classify_token(pptoken),
                location: SourceSpan {
                    start: pptoken.location,
                    end: SourceLoc::new(
                        pptoken.location.source_id(),
                        pptoken.location.offset() + pptoken.length as u32,
                    ),
                },
            };

            if let TokenKind::StringLiteral(symbol) = token.kind {
                // Optimization: Avoid allocation for single string literals.
                // Peek ahead to see if the next token is also a string literal.
                // If so, we need to concatenate them, which requires allocation.
                if let Some(next_pptoken) = current_token_iter.peek()
                    && let PPTokenKind::StringLiteral(_) = next_pptoken.kind
                {
                    // ⚡ Bolt: Optimized string concatenation.
                    // The previous implementation performed multiple string allocations and copies.
                    // This version calculates the total required size first, performs a single
                    // allocation, and then appends the string contents. This significantly
                    // reduces memory allocations and improves performance for code with many
                    // adjacent string literals.

                    // Collect all adjacent string literal symbols first.
                    let mut symbols_to_concat = vec![symbol];
                    let mut end_location = token.location.end;

                    while let Some(next_pptoken) = current_token_iter.peek() {
                        if let PPTokenKind::StringLiteral(next_symbol) = next_pptoken.kind {
                            let consumed_pptoken = current_token_iter.next().unwrap();
                            end_location = SourceLoc::new(
                                consumed_pptoken.location.source_id(),
                                consumed_pptoken.location.offset() + consumed_pptoken.length as u32,
                            );
                            symbols_to_concat.push(next_symbol);
                        } else {
                            break;
                        }
                    }

                    // Calculate the total length of the final string for a single allocation.
                    let total_len = symbols_to_concat
                        .iter()
                        .map(|s| Self::extract_string_content(s).unwrap_or("").len())
                        .sum();

                    // Allocate the string with the exact capacity and build it.
                    let mut content = String::with_capacity(total_len);
                    for s in symbols_to_concat {
                        if let Some(s_content) = Self::extract_string_content(&s) {
                            content.push_str(s_content);
                        }
                    }

                    // Create a new symbol with the concatenated content and update the token.
                    token.kind = TokenKind::StringLiteral(Symbol::new(format!("\"{}\"", content)));
                    token.location.end = end_location;
                }
                // If the next token is not a string literal, we do nothing. The original,
                // un-concatenated StringLiteral token is used, avoiding any string allocation.
            }

            let is_eof = matches!(token.kind, TokenKind::EndOfFile);
            tokens.push(token);
            if is_eof {
                break;
            }
        }

        tokens
    }

    /// Parse C11 floating-point literal syntax
    fn parse_c11_float_literal(&self, text: Symbol) -> Result<f64, ()> {
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
            self.parse_hex_float_literal(text_without_suffix)
        } else {
            // Use Rust's built-in parsing for decimal floats
            match text_without_suffix.parse::<f64>() {
                Ok(val) => Ok(val),
                Err(_) => {
                    // Invalid float, treat as unknown
                    Err(())
                }
            }
        }
    }

    /// Parse hexadecimal floating-point literal (C99/C11)
    fn parse_hex_float_literal(&self, text: &str) -> Result<f64, ()> {
        // Format: 0[xX][hexdigits][.hexdigits][pP[+|-]digits][fFlL]
        // Example: 0x1.2p3, 0x1p-5f, 0x.8p10L

        let mut chars = text.chars().peekable();
        let mut result = 0.0f64;
        let mut exponent = 0i32;
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
                return Err(());
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
                    return Err(());
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

            // Parse exponent digits safely without string allocation
            let mut exp_val = 0i32;
            let mut exp_digits = 0;
            while let Some(&c) = chars.peek() {
                if let Some(digit) = c.to_digit(10) {
                    // Use checked arithmetic to prevent overflow, replicating .parse() behavior.
                    exp_val = match exp_val.checked_mul(10).and_then(|v| v.checked_add(digit as i32)) {
                        Some(val) => val,
                        None => return Err(()), // Overflow
                    };
                    exp_digits += 1;
                    chars.next();
                } else {
                    break;
                }
            }

            if exp_digits == 0 {
                return Err(());
            }

            exponent = if exp_negative { -exp_val } else { exp_val };
        }

        // Apply fractional adjustment
        if fraction_digits > 0 {
            result /= 16.0f64.powi(fraction_digits);
        }

        // Apply binary exponent
        if exponent != 0 {
            result *= 2.0f64.powi(exponent);
        }

        Ok(result)
    }

    /// Extract content from a string literal symbol, removing quotes
    fn extract_string_content(symbol: &Symbol) -> Option<&str> {
        let s = symbol.as_str();
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            Some(&s[1..s.len() - 1])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests_lexer;
