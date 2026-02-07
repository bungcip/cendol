use crate::ast::StringId;
use crate::ast::literal::{FloatSuffix, IntegerSuffix};
use crate::ast::literal_parsing;
use crate::pp::{PPToken, PPTokenKind};
use crate::source_manager::SourceSpan;

use serde::Serialize;
/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum TokenKind {
    // === LITERALS ===
    IntegerConstant(i64, Option<IntegerSuffix>), // Parsed integer literal value
    FloatConstant(f64, Option<FloatSuffix>),     // Parsed float literal value
    CharacterConstant(u64),                      // Value of character constant
    StringLiteral(StringId),                     // Interned string literal

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
    BuiltinVaArg,
    BuiltinVaList,
    BuiltinVaStart,
    BuiltinVaEnd,
    BuiltinVaCopy,
    BuiltinExpect,

    // Atomic builtins
    BuiltinAtomicLoadN,
    BuiltinAtomicStoreN,
    BuiltinAtomicExchangeN,
    BuiltinAtomicCompareExchangeN,
    BuiltinAtomicFetchAdd,
    BuiltinAtomicFetchSub,
    BuiltinAtomicFetchAnd,
    BuiltinAtomicFetchOr,
    BuiltinAtomicFetchXor,

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
    pub(crate) fn is_storage_class_specifier(&self) -> bool {
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
    pub(crate) fn is_type_specifier(&self) -> bool {
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
                | TokenKind::BuiltinVaList
        )
    }

    /// Check if the token is a type qualifier
    pub(crate) fn is_type_qualifier(&self) -> bool {
        matches!(
            self,
            TokenKind::Const | TokenKind::Restrict | TokenKind::Volatile | TokenKind::Atomic
        )
    }

    /// Check if the token is a function specifier
    pub(crate) fn is_function_specifier(&self) -> bool {
        matches!(self, TokenKind::Inline | TokenKind::Noreturn)
    }

    /// Check if the token is an alignment specifier
    pub(crate) fn is_alignment_specifier(&self) -> bool {
        matches!(self, TokenKind::Alignas)
    }

    /// Check if the token can start a declaration specifier
    pub(crate) fn is_declaration_specifier_start(&self) -> bool {
        self.is_storage_class_specifier()
            || self.is_type_specifier()
            || self.is_type_qualifier()
            || self.is_function_specifier()
            || self.is_alignment_specifier()
            || matches!(self, TokenKind::Attribute)
    }

    /// Check if the token can start a declaration (including typedefs)
    pub(crate) fn is_declaration_start(&self, is_typedef: bool) -> bool {
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
pub(crate) fn is_keyword(symbol: StringId) -> Option<TokenKind> {
    keyword_map().get(&symbol).copied()
}

fn keyword_map() -> &'static hashbrown::HashMap<StringId, TokenKind> {
    static KEYWORDS: std::sync::OnceLock<hashbrown::HashMap<StringId, TokenKind>> = std::sync::OnceLock::new();
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
        m.insert(StringId::new("__builtin_va_arg"), TokenKind::BuiltinVaArg);
        m.insert(StringId::new("__builtin_va_list"), TokenKind::BuiltinVaList);
        m.insert(StringId::new("__builtin_va_start"), TokenKind::BuiltinVaStart);
        m.insert(StringId::new("__builtin_va_end"), TokenKind::BuiltinVaEnd);
        m.insert(StringId::new("__builtin_va_copy"), TokenKind::BuiltinVaCopy);
        m.insert(StringId::new("__builtin_expect"), TokenKind::BuiltinExpect);
        m.insert(StringId::new("__atomic_load_n"), TokenKind::BuiltinAtomicLoadN);
        m.insert(StringId::new("__atomic_store_n"), TokenKind::BuiltinAtomicStoreN);
        m.insert(StringId::new("__atomic_exchange_n"), TokenKind::BuiltinAtomicExchangeN);
        m.insert(
            StringId::new("__atomic_compare_exchange_n"),
            TokenKind::BuiltinAtomicCompareExchangeN,
        );
        m.insert(StringId::new("__atomic_fetch_add"), TokenKind::BuiltinAtomicFetchAdd);
        m.insert(StringId::new("__atomic_fetch_sub"), TokenKind::BuiltinAtomicFetchSub);
        m.insert(StringId::new("__atomic_fetch_and"), TokenKind::BuiltinAtomicFetchAnd);
        m.insert(StringId::new("__atomic_fetch_or"), TokenKind::BuiltinAtomicFetchOr);
        m.insert(StringId::new("__atomic_fetch_xor"), TokenKind::BuiltinAtomicFetchXor);
        m
    })
}

/// Lexer state machine
pub struct Lexer<'src> {
    // Current position in token stream
    tokens: &'src [PPToken],
}

impl<'src> Lexer<'src> {
    /// Create a new lexer with the given preprocessor token stream
    pub fn new(tokens: &'src [PPToken]) -> Self {
        Lexer { tokens }
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
                if let Some((int_val, suffix)) = literal_parsing::parse_c11_integer_literal(value.as_str()) {
                    TokenKind::IntegerConstant(int_val as i64, suffix)
                } else if let Some((float_val, suffix)) = literal_parsing::parse_c11_float_literal(value.as_str()) {
                    TokenKind::FloatConstant(float_val, suffix)
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
        // Bolt ⚡: Pre-allocate the tokens vector with the capacity of the preprocessor tokens.
        // This is a reasonable estimate that reduces the number of reallocations,
        // as the number of lexical tokens is usually similar to the number of preprocessor tokens.
        let mut tokens = Vec::with_capacity(self.tokens.len());
        let mut current_token_iter = self.tokens.iter().peekable();

        while let Some(pptoken) = current_token_iter.next() {
            if let PPTokenKind::StringLiteral(symbol) = pptoken.kind {
                // ⚡ Bolt: Optimized string literal handling.
                // This introduces a fast path for single string literals, which are the
                // most common case. By peeking ahead, we avoid the overhead of the
                // two-pass concatenation logic unless it's actually needed. This
                // reduces overhead and improves lexer performance.

                // --- Fast path for single string literals ---
                if !matches!(
                    current_token_iter.peek(),
                    Some(PPToken {
                        kind: PPTokenKind::StringLiteral(_),
                        ..
                    })
                ) {
                    tokens.push(Token {
                        kind: self.classify_token(pptoken),
                        span: SourceSpan::new_with_length(
                            pptoken.location.source_id(),
                            pptoken.location.offset(),
                            pptoken.length as u32,
                        ),
                    });
                    continue;
                }

                // --- Slow path: Concatenate adjacent string literals ---
                let start_span = SourceSpan::new_with_length(
                    pptoken.location.source_id(),
                    pptoken.location.offset(),
                    pptoken.length as u32,
                );
                let mut final_span = start_span;

                // --- Phase 1: Determine final prefix and total size ---
                let (mut prefix, first_content) = Self::extract_literal_parts(symbol.as_str()).unwrap_or(("", ""));

                // Concatenate raw content (inside quotes)
                let mut concatenated_content = String::with_capacity(first_content.len() * 2);
                concatenated_content.push_str(first_content);

                let mut adjacent_literals = 0;
                let next_token_idx = self.tokens.len() - current_token_iter.len();

                while let Some(next_pptoken) = self.tokens.get(next_token_idx + adjacent_literals) {
                    if let PPTokenKind::StringLiteral(next_symbol) = next_pptoken.kind {
                        let (next_prefix, next_content) =
                            Self::extract_literal_parts(next_symbol.as_str()).unwrap_or(("", ""));

                        if prefix.is_empty() && !next_prefix.is_empty() {
                            prefix = next_prefix;
                        }

                        concatenated_content.push_str(next_content);

                        final_span = SourceSpan::new_with_length(
                            next_pptoken.location.source_id(),
                            next_pptoken.location.offset(),
                            next_pptoken.length as u32,
                        );
                        adjacent_literals += 1;
                    } else {
                        break;
                    }
                }

                // --- Phase 2: Consume tokens ---
                for _ in 0..adjacent_literals {
                    current_token_iter.next();
                }

                // Construct final literal: prefix + " + content + "
                let mut final_literal = String::with_capacity(concatenated_content.len() + prefix.len() + 2);
                final_literal.push_str(prefix);
                final_literal.push('"');
                final_literal.push_str(&concatenated_content);
                final_literal.push('"');

                tokens.push(Token {
                    kind: TokenKind::StringLiteral(StringId::new(final_literal)),
                    span: start_span.merge(final_span),
                });
                continue;
            }

            // For all other tokens, process normally
            let token = Token {
                kind: self.classify_token(pptoken),
                span: SourceSpan::new_with_length(
                    pptoken.location.source_id(),
                    pptoken.location.offset(),
                    pptoken.length as u32,
                ),
            };

            let is_eof = matches!(token.kind, TokenKind::EndOfFile);
            tokens.push(token);
            if is_eof {
                break;
            }
        }

        tokens
    }

    /// Extract parts from a string literal symbol: (prefix, content_without_quotes)
    fn extract_literal_parts(s: &str) -> Option<(&str, &str)> {
        if let Some(rest) = s.strip_prefix("L\"") {
            if let Some(inner) = rest.strip_suffix('"') {
                return Some(("L", inner));
            }
        } else if let Some(rest) = s.strip_prefix("u\"") {
            if let Some(inner) = rest.strip_suffix('"') {
                return Some(("u", inner));
            }
        } else if let Some(rest) = s.strip_prefix("U\"") {
            if let Some(inner) = rest.strip_suffix('"') {
                return Some(("U", inner));
            }
        } else if let Some(rest) = s.strip_prefix("u8\"") {
            if let Some(inner) = rest.strip_suffix('"') {
                return Some(("u8", inner));
            }
        } else if let Some(rest) = s.strip_prefix("\"")
            && let Some(inner) = rest.strip_suffix('"')
        {
            return Some(("", inner));
        }
        None
    }
}
