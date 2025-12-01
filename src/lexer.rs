use crate::pp::{PPToken, PPTokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use symbol_table::GlobalSymbol as Symbol;

use hashbrown::HashMap;
use std::sync::OnceLock;

// Re-export DiagnosticEngine from diagnostic module for convenience
pub use crate::diagnostic::DiagnosticEngine;

/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // === LITERALS ===
    IntegerConstant(i64),  // Parsed integer literal value
    FloatConstant(Symbol), // Raw float literal text
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

/// Token with source location for the parser
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        let lower_text = text.to_lowercase();

        // Check for suffixes in order of length (longest first)
        if lower_text.ends_with("ull") || lower_text.ends_with("llu") {
            &text[..text.len() - 3]
        } else if lower_text.ends_with("ul") || lower_text.ends_with("lu") || lower_text.ends_with("ll") {
            &text[..text.len() - 2]
        } else if lower_text.ends_with('u') || lower_text.ends_with('l') {
            &text[..text.len() - 1]
        } else {
            text
        }
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
                // Try to parse as integer first
                self.parse_c11_integer_literal(value)
                    .map(TokenKind::IntegerConstant)
                    .unwrap_or_else(|_| TokenKind::FloatConstant(value))
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
        while let Some(token) = self.next_token() {
            tokens.push(token);
            if matches!(token.kind, TokenKind::EndOfFile) {
                break;
            }
        }

        // Perform string literal concatenation (C11 6.4.5)
        tokens = self.concatenate_string_literals(tokens);

        tokens
    }

    /// Concatenate adjacent string literals (C11 6.4.5)
    fn concatenate_string_literals(&self, tokens: Vec<Token>) -> Vec<Token> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < tokens.len() {
            if let TokenKind::StringLiteral(_) = tokens[i].kind {
                // Try to concatenate string literals starting from position i
                let (concatenated_token, next_pos) = self.concatenate_from_position(&tokens, i);
                result.push(concatenated_token);
                i = next_pos;
            } else {
                result.push(tokens[i]);
                i += 1;
            }
        }

        result
    }

    /// Concatenate string literals starting from a given position
    fn concatenate_from_position(&self, tokens: &[Token], start_pos: usize) -> (Token, usize) {
        let mut content = String::new();
        let start_location = tokens[start_pos].location.start;
        let mut end_location = tokens[start_pos].location.end;
        let mut pos = start_pos;

        // Collect all adjacent string literals
        while pos < tokens.len() {
            if let TokenKind::StringLiteral(symbol) = &tokens[pos].kind {
                if let Some(extracted) = Self::extract_string_content(symbol) {
                    content.push_str(&extracted);
                    end_location = tokens[pos].location.end;
                    pos += 1;
                } else {
                    // Invalid format, stop concatenation
                    break;
                }
            } else {
                // Not a string literal, stop concatenation
                break;
            }
        }

        // Create the concatenated token
        let final_string = format!("\"{}\"", content);
        let concatenated_symbol = Symbol::new(&final_string);
        let token = Token {
            kind: TokenKind::StringLiteral(concatenated_symbol),
            location: SourceSpan {
                start: start_location,
                end: end_location,
            },
        };

        (token, pos)
    }

    /// Extract content from a string literal symbol, removing quotes
    fn extract_string_content(symbol: &Symbol) -> Option<String> {
        let s = symbol.as_str();
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            Some(s[1..s.len() - 1].to_string())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests_lexer;
