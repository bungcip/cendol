use crate::intern::StringId;
use crate::pp::{PPToken, PPTokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};

/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    // === LITERALS ===
    IntegerConstant(i64),    // Parsed integer literal value
    FloatConstant(f64),      // Parsed float literal value
    CharacterConstant(u8),   // Byte value of character constant
    StringLiteral(StringId), // Interned string literal

    // === IDENTIFIERS ===
    Identifier(StringId), // Interned identifier

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
        matches!(
            self,
            TokenKind::Const | TokenKind::Restrict | TokenKind::Volatile | TokenKind::Atomic
        )
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
        if self.is_declaration_specifier_start() || *self == TokenKind::StaticAssert {
            return true;
        }

        if let TokenKind::Identifier(_) = self {
            return is_typedef;
        }

        false
    }
}

/// Token with source span for the parser
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: SourceSpan,
}

/// Classify a preprocessor punctuation token into a lexical token.
///
/// ⚡ Bolt: Optimized with a `match` statement.
/// This is significantly faster than the previous `HashMap` implementation because
/// the Rust compiler can optimize it into a perfect hash table or a more direct
/// jump table, avoiding the overhead of runtime hashing and lookups.
fn classify_punctuation(pp_token_kind: PPTokenKind) -> TokenKind {
    match pp_token_kind {
        // Arithmetic operators
        PPTokenKind::Plus => TokenKind::Plus,
        PPTokenKind::Minus => TokenKind::Minus,
        PPTokenKind::Star => TokenKind::Star,
        PPTokenKind::Slash => TokenKind::Slash,
        PPTokenKind::Percent => TokenKind::Percent,
        PPTokenKind::Increment => TokenKind::Increment,
        PPTokenKind::Decrement => TokenKind::Decrement,

        // Bitwise operators
        PPTokenKind::And => TokenKind::And,
        PPTokenKind::Or => TokenKind::Or,
        PPTokenKind::Xor => TokenKind::Xor,
        PPTokenKind::Not => TokenKind::Not,
        PPTokenKind::Tilde => TokenKind::Tilde,
        PPTokenKind::LeftShift => TokenKind::LeftShift,
        PPTokenKind::RightShift => TokenKind::RightShift,

        // Comparison operators
        PPTokenKind::Less => TokenKind::Less,
        PPTokenKind::Greater => TokenKind::Greater,
        PPTokenKind::LessEqual => TokenKind::LessEqual,
        PPTokenKind::GreaterEqual => TokenKind::GreaterEqual,
        PPTokenKind::Equal => TokenKind::Equal,
        PPTokenKind::NotEqual => TokenKind::NotEqual,

        // Assignment operators
        PPTokenKind::Assign => TokenKind::Assign,
        PPTokenKind::PlusAssign => TokenKind::PlusAssign,
        PPTokenKind::MinusAssign => TokenKind::MinusAssign,
        PPTokenKind::StarAssign => TokenKind::StarAssign,
        PPTokenKind::DivAssign => TokenKind::DivAssign,
        PPTokenKind::ModAssign => TokenKind::ModAssign,
        PPTokenKind::AndAssign => TokenKind::AndAssign,
        PPTokenKind::OrAssign => TokenKind::OrAssign,
        PPTokenKind::XorAssign => TokenKind::XorAssign,
        PPTokenKind::LeftShiftAssign => TokenKind::LeftShiftAssign,
        PPTokenKind::RightShiftAssign => TokenKind::RightShiftAssign,

        // Logical operators
        PPTokenKind::LogicAnd => TokenKind::LogicAnd,
        PPTokenKind::LogicOr => TokenKind::LogicOr,

        // Member access
        PPTokenKind::Arrow => TokenKind::Arrow,
        PPTokenKind::Dot => TokenKind::Dot,

        // Ternary operator
        PPTokenKind::Question => TokenKind::Question,
        PPTokenKind::Colon => TokenKind::Colon,

        // Punctuation
        PPTokenKind::Comma => TokenKind::Comma,
        PPTokenKind::Semicolon => TokenKind::Semicolon,
        PPTokenKind::Ellipsis => TokenKind::Ellipsis,

        // Brackets and parentheses
        PPTokenKind::LeftParen => TokenKind::LeftParen,
        PPTokenKind::RightParen => TokenKind::RightParen,
        PPTokenKind::LeftBracket => TokenKind::LeftBracket,
        PPTokenKind::RightBracket => TokenKind::RightBracket,
        PPTokenKind::LeftBrace => TokenKind::LeftBrace,
        PPTokenKind::RightBrace => TokenKind::RightBrace,

        // Tokens that don't map directly to a parser token
        PPTokenKind::Hash | PPTokenKind::HashHash => TokenKind::Unknown,

        // Non-punctuation tokens are not handled by this function
        _ => TokenKind::Unknown,
    }
}

/// Check if a symbol represents a C11 keyword.
///
/// ⚡ Bolt: Optimized with a pre-initialized `HashMap`.
/// This is significantly faster than the previous match-based implementation, which
/// required converting the `StringId` to a `&str` for every lookup. This version
// pre-interns all keywords and stores them in a lazily-initialized `HashMap`.
/// Subsequent lookups use the `StringId` directly, resulting in a much faster
/// integer comparison instead of a string comparison.
pub fn is_keyword(symbol: StringId) -> Option<TokenKind> {
    keyword_map().get(&symbol).copied()
}

fn keyword_map() -> &'static hashbrown::HashMap<StringId, TokenKind> {
    static KEYWORDS: std::sync::OnceLock<hashbrown::HashMap<StringId, TokenKind>> =
        std::sync::OnceLock::new();
    KEYWORDS.get_or_init(|| {
        let mut m = hashbrown::HashMap::new();
        m.insert(StringId::new("auto"), TokenKind::Auto);
        m.insert(StringId::new("break"), TokenKind::Break);
        m.insert(StringId::new("case"), TokenKind::Case);
        m.insert(StringId::new("char"), TokenKind::Char);
        m.insert(StringId::new("const"), TokenKind::Const);
        m.insert(StringId::new("continue"), TokenKind::Continue);
        m.insert(StringId::new("default"), TokenKind::Default);
        m.insert(StringId::new("do"), TokenKind::Do);
        m.insert(StringId::new("double"), TokenKind::Double);
        m.insert(StringId::new("else"), TokenKind::Else);
        m.insert(StringId::new("enum"), TokenKind::Enum);
        m.insert(StringId::new("extern"), TokenKind::Extern);
        m.insert(StringId::new("float"), TokenKind::Float);
        m.insert(StringId::new("for"), TokenKind::For);
        m.insert(StringId::new("goto"), TokenKind::Goto);
        m.insert(StringId::new("if"), TokenKind::If);
        m.insert(StringId::new("inline"), TokenKind::Inline);
        m.insert(StringId::new("int"), TokenKind::Int);
        m.insert(StringId::new("long"), TokenKind::Long);
        m.insert(StringId::new("register"), TokenKind::Register);
        m.insert(StringId::new("restrict"), TokenKind::Restrict);
        m.insert(StringId::new("return"), TokenKind::Return);
        m.insert(StringId::new("short"), TokenKind::Short);
        m.insert(StringId::new("signed"), TokenKind::Signed);
        m.insert(StringId::new("sizeof"), TokenKind::Sizeof);
        m.insert(StringId::new("static"), TokenKind::Static);
        m.insert(StringId::new("struct"), TokenKind::Struct);
        m.insert(StringId::new("switch"), TokenKind::Switch);
        m.insert(StringId::new("typedef"), TokenKind::Typedef);
        m.insert(StringId::new("union"), TokenKind::Union);
        m.insert(StringId::new("unsigned"), TokenKind::Unsigned);
        m.insert(StringId::new("void"), TokenKind::Void);
        m.insert(StringId::new("volatile"), TokenKind::Volatile);
        m.insert(StringId::new("while"), TokenKind::While);
        m.insert(StringId::new("_Alignas"), TokenKind::Alignas);
        m.insert(StringId::new("_Alignof"), TokenKind::Alignof);
        m.insert(StringId::new("_Atomic"), TokenKind::Atomic);
        m.insert(StringId::new("_Bool"), TokenKind::Bool);
        m.insert(StringId::new("_Complex"), TokenKind::Complex);
        m.insert(StringId::new("_Generic"), TokenKind::Generic);
        m.insert(StringId::new("_Noreturn"), TokenKind::Noreturn);
        m.insert(StringId::new("_Pragma"), TokenKind::Pragma);
        m.insert(StringId::new("_Static_assert"), TokenKind::StaticAssert);
        m.insert(StringId::new("_Thread_local"), TokenKind::ThreadLocal);
        m.insert(StringId::new("__attribute__"), TokenKind::Attribute);
        m.insert(StringId::new("__attribute"), TokenKind::Attribute);
        m
    })
}

/// Lexer state machine
pub struct Lexer<'src> {
    // Current position in token stream
    tokens: &'src [PPToken],
    // current_index: usize,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer with the given preprocessor token stream
    pub fn new(tokens: &'src [PPToken]) -> Self {
        Lexer {
            tokens,
            // current_index: 0,
        }
    }

    /// Parse C11 integer literal syntax
    ///
    /// ⚡ Bolt: Optimized integer parsing.
    /// This implementation is faster than the previous version. It first uses the
    /// existing optimized `strip_integer_suffix` function, then replaces the multi-step
    /// `extract_digits_and_base` and `parse_integer_value` (which used slower
    /// general-purpose parsing functions) with a single, direct parsing loop.
    /// This avoids intermediate allocations and improves performance by using
    /// checked arithmetic directly on the string's characters.
    fn parse_c11_integer_literal(&self, text: StringId) -> Result<i64, ()> {
        let text_str = text.as_str();

        // Use the existing, optimized suffix stripper to get the numeric part.
        let number_part = Self::strip_integer_suffix(text_str);

        // Handle the case where the number is just "0" after stripping suffix.
        if number_part == "0" {
            return Ok(0);
        }

        let mut base = 10;
        let mut digits_to_parse = number_part;

        // Determine base and strip prefix from the numeric part.
        if number_part.starts_with("0x") || number_part.starts_with("0X") {
            base = 16;
            digits_to_parse = &number_part[2..];
        } else if let Some(stripped) = number_part.strip_prefix('0') {
            base = 8;
            digits_to_parse = stripped;
        }
        // else base is 10 and we parse the whole `number_part`.

        // If after stripping prefixes the string is empty, it's an error.
        if digits_to_parse.is_empty() {
            return Err(());
        }

        let mut result: u64 = 0;
        for c in digits_to_parse.chars() {
            // `to_digit` will return None for invalid characters in the given base
            // (e.g., '9' in octal), which correctly propagates the error.
            let digit = c.to_digit(base).ok_or(())?;

            // Use checked arithmetic to prevent overflow, replicating .parse() behavior.
            result = result.checked_mul(base as u64).ok_or(())?;
            result = result.checked_add(digit as u64).ok_or(())?;
        }

        Ok(result as i64)
    }

    /// Strip integer literal suffix (u, l, ll, ul, ull, etc.)
    fn strip_integer_suffix(text: &str) -> &str {
        // ⚡ Bolt: Optimized suffix stripping.
        // This implementation is faster than the previous version, which used multiple
        // string slices and `eq_ignore_ascii_case` calls. By working with bytes directly
        // and using `matches!` for character comparisons, we avoid the overhead of
        // slicing and function calls in the common cases, resulting in a small but
        // measurable performance improvement for parsing integer literals.
        let bytes = text.as_bytes();
        let len = bytes.len();

        if len == 0 {
            return text;
        }

        // Check for the longest suffixes first (3 characters: "ull", "llu").
        if len >= 3 {
            let last3 = (
                bytes[len - 3].to_ascii_lowercase(),
                bytes[len - 2].to_ascii_lowercase(),
                bytes[len - 1].to_ascii_lowercase(),
            );
            if matches!(last3, (b'u', b'l', b'l') | (b'l', b'l', b'u')) {
                return &text[..len - 3];
            }
        }

        // Check for 2-character suffixes ("ul", "lu", "ll").
        if len >= 2 {
            let last2 = (bytes[len - 2].to_ascii_lowercase(), bytes[len - 1].to_ascii_lowercase());
            if matches!(last2, (b'u', b'l') | (b'l', b'u') | (b'l', b'l')) {
                return &text[..len - 2];
            }
        }

        // Check for 1-character suffixes ("u", "l").
        if len >= 1 {
            let last1 = bytes[len - 1].to_ascii_lowercase();
            if matches!(last1, b'u' | b'l') {
                return &text[..len - 1];
            }
        }

        // No suffix found.
        text
    }

    /// Classify a preprocessor token into a lexical token
    fn classify_token(&self, pptoken: &PPToken) -> TokenKind {
        match pptoken.kind {
            PPTokenKind::Identifier(symbol) => {
                // Check if it's a keyword
                is_keyword(symbol).unwrap_or(TokenKind::Identifier(symbol))
            }
            PPTokenKind::StringLiteral(symbol) => {
                // Strip quotes from string literal
                if let Some(content) = Self::extract_string_content(&symbol) {
                    TokenKind::StringLiteral(StringId::new(content))
                } else {
                    TokenKind::StringLiteral(symbol)
                }
            }
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
            // Handle punctuation tokens using the optimized match-based function
            pptoken_kind => classify_punctuation(pptoken_kind),
        }
    }

    /// Get all tokens from the stream
    pub fn tokenize_all(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        let mut current_token_iter = self.tokens.iter().peekable();

        while let Some(pptoken) = current_token_iter.next() {
            // ⚡ Bolt: Optimized string literal concatenation.
            // This implementation avoids intermediate allocations and multiple passes.
            // When a string literal is found, it initializes a buffer and immediately
            // starts consuming subsequent adjacent string literals, appending their
            // content in a single pass. This is more efficient than the previous
            // method of collecting tokens into a vector and iterating over it multiple
            // times.
            if let PPTokenKind::StringLiteral(symbol) = pptoken.kind {
                let start_location = pptoken.location;
                let mut end_location = SourceLoc::new(
                    pptoken.location.source_id(),
                    pptoken.location.offset() + pptoken.length as u32,
                );

                // Initialize content with the first string literal's content
                let mut content = Self::extract_string_content(&symbol).unwrap_or("").to_string();

                // Peek ahead and consume all adjacent string literals
                while let Some(next_pptoken) = current_token_iter.peek() {
                    if let PPTokenKind::StringLiteral(next_symbol) = next_pptoken.kind {
                        // It's a string literal, so consume it
                        let consumed_pptoken = current_token_iter.next().unwrap();
                        if let Some(s_content) = Self::extract_string_content(&next_symbol) {
                            content.push_str(s_content);
                        }
                        end_location = SourceLoc::new(
                            consumed_pptoken.location.source_id(),
                            consumed_pptoken.location.offset() + consumed_pptoken.length as u32,
                        );
                    } else {
                        // Not a string literal, stop concatenating
                        break;
                    }
                }

                // Create a single concatenated token
                let concatenated_token = Token {
                    kind: TokenKind::StringLiteral(StringId::new(content)),
                    span: SourceSpan {
                        start: start_location,
                        end: end_location,
                    },
                };

                tokens.push(concatenated_token);
                continue; // Continue to the next token in the input stream
            }

            // For all other tokens, process normally
            let token = Token {
                kind: self.classify_token(pptoken),
                span: SourceSpan {
                    start: pptoken.location,
                    end: SourceLoc::new(
                        pptoken.location.source_id(),
                        pptoken.location.offset() + pptoken.length as u32,
                    ),
                },
            };

            let is_eof = matches!(token.kind, TokenKind::EndOfFile);
            tokens.push(token);
            if is_eof {
                break;
            }
        }

        tokens
    }

    /// Parse C11 floating-point literal syntax
    fn parse_c11_float_literal(&self, text: StringId) -> Result<f64, ()> {
        let text_str = text.as_str();

        // C11 floating-point literal format:
        // [digits][.digits][e|E[+|-]digits][f|F|l|L]
        // or [digits][e|E[+|-]digits][f|F|l|L]
        // or 0[xX][hexdigits][.hexdigits][p|P[+|-]digits][f|F|l|L]

        // ⚡ Bolt: Optimized suffix stripping.
        // This is faster than chaining `ends_with` calls. By checking the last byte
        // directly, we avoid multiple string traversals and improve performance for
        // parsing floating-point literals.
        let text_without_suffix = if !text_str.is_empty() {
            match text_str.as_bytes()[text_str.len() - 1] {
                b'f' | b'F' | b'l' | b'L' => &text_str[..text_str.len() - 1],
                _ => text_str,
            }
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
    fn extract_string_content(symbol: &StringId) -> Option<&str> {
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
