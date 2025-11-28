use crate::lang_options::LangOptions;
use crate::pp::{PPToken, PPTokenKind};
use crate::source_manager::{SourceLoc, SourceManager, SourceSpan};
use symbol_table::GlobalSymbol as Symbol;
use target_lexicon::Triple as TargetTriple;

// Re-export DiagnosticEngine from diagnostic module for convenience
pub use crate::diagnostic::DiagnosticEngine;

/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Literals
    IntegerConstant(i64),   // Parsed integer literal value
    FloatConstant(Symbol),  // Raw float literal text
    CharacterConstant(u8),  // Byte value of character constant
    StringLiteral(Symbol),  // Interned string literal

    // Keywords (C11)
    Auto,
    Break,
    Case,
    Char,
    Const,
    Continue,
    Default,
    Do,
    Double,
    Else,
    Enum,
    Extern,
    Float,
    For,
    Goto,
    If,
    Inline,
    Int,
    Long,
    Register,
    Restrict,
    Return,
    Short,
    Signed,
    Sizeof,
    Static,
    Struct,
    Switch,
    Typedef,
    Union,
    Unsigned,
    Void,
    Volatile,
    While,
    // C11 specific keywords
    Alignas,
    Alignof,
    Atomic,
    Bool,
    Complex,
    Generic,
    Noreturn,
    Pragma,
    StaticAssert,
    ThreadLocal,

    // Identifiers
    Identifier(Symbol), // Interned identifier

    // Operators and punctuation
    Plus,
    Minus,
    Star,
    Slash,
    Percent, // + - * / %
    And,
    Or,
    Xor,
    Not,
    Tilde, // & | ^ ! ~
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual, // < > <= >= == !=
    LeftShift,
    RightShift, // << >>
    Assign,
    PlusAssign,
    MinusAssign, // = += -=
    StarAssign,
    DivAssign,
    ModAssign, // *= /= %=
    AndAssign,
    OrAssign,
    XorAssign, // &= |= ^=
    LeftShiftAssign,
    RightShiftAssign, // <<= >>=
    Increment,
    Decrement, // ++ --
    Arrow,
    Dot, // -> .
    Question,
    Colon, // ? :
    Comma,
    Semicolon, // , ;
    LeftParen,
    RightParen, // ( )
    LeftBracket,
    RightBracket, // [ ]
    LeftBrace,
    RightBrace, // { }
    Ellipsis,   // ...
    LogicAnd,
    LogicOr, // && ||

    // Special tokens
    EndOfFile,
    Unknown,
}

/// Token with source location for the parser
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub location: SourceSpan,
}

/// Table of pre-interned C11 keywords for O(1) keyword recognition
pub struct KeywordTable {
    // C11 keywords
    auto: Symbol,
    break_: Symbol,
    case: Symbol,
    char_: Symbol,
    const_: Symbol,
    continue_: Symbol,
    default: Symbol,
    do_: Symbol,
    double: Symbol,
    else_: Symbol,
    enum_: Symbol,
    extern_: Symbol,
    float: Symbol,
    for_: Symbol,
    goto: Symbol,
    if_: Symbol,
    inline: Symbol,
    int: Symbol,
    long: Symbol,
    register: Symbol,
    restrict: Symbol,
    return_: Symbol,
    short: Symbol,
    signed: Symbol,
    sizeof: Symbol,
    static_: Symbol,
    struct_: Symbol,
    switch: Symbol,
    typedef: Symbol,
    union_: Symbol,
    unsigned: Symbol,
    void: Symbol,
    volatile: Symbol,
    while_: Symbol,
    // C11 specific
    alignas: Symbol,
    alignof: Symbol,
    atomic: Symbol,
    bool_: Symbol,
    complex: Symbol,
    generic: Symbol,
    noreturn: Symbol,
    pragma: Symbol,
    static_assert: Symbol,
    thread_local: Symbol,
}

impl Default for KeywordTable {
    fn default() -> Self {
        Self::new()
    }
}

impl KeywordTable {
    pub fn new() -> Self {
        KeywordTable {
            auto: Symbol::new("auto"),
            break_: Symbol::new("break"),
            case: Symbol::new("case"),
            char_: Symbol::new("char"),
            const_: Symbol::new("const"),
            continue_: Symbol::new("continue"),
            default: Symbol::new("default"),
            do_: Symbol::new("do"),
            double: Symbol::new("double"),
            else_: Symbol::new("else"),
            enum_: Symbol::new("enum"),
            extern_: Symbol::new("extern"),
            float: Symbol::new("float"),
            for_: Symbol::new("for"),
            goto: Symbol::new("goto"),
            if_: Symbol::new("if"),
            inline: Symbol::new("inline"),
            int: Symbol::new("int"),
            long: Symbol::new("long"),
            register: Symbol::new("register"),
            restrict: Symbol::new("restrict"),
            return_: Symbol::new("return"),
            short: Symbol::new("short"),
            signed: Symbol::new("signed"),
            sizeof: Symbol::new("sizeof"),
            static_: Symbol::new("static"),
            struct_: Symbol::new("struct"),
            switch: Symbol::new("switch"),
            typedef: Symbol::new("typedef"),
            union_: Symbol::new("union"),
            unsigned: Symbol::new("unsigned"),
            void: Symbol::new("void"),
            volatile: Symbol::new("volatile"),
            while_: Symbol::new("while"),
            // C11 specific
            alignas: Symbol::new("_Alignas"),
            alignof: Symbol::new("_Alignof"),
            atomic: Symbol::new("_Atomic"),
            bool_: Symbol::new("_Bool"),
            complex: Symbol::new("_Complex"),
            generic: Symbol::new("_Generic"),
            noreturn: Symbol::new("_Noreturn"),
            pragma: Symbol::new("_Pragma"),
            static_assert: Symbol::new("_Static_assert"),
            thread_local: Symbol::new("_Thread_local"),
        }
    }

    pub fn is_keyword(&self, symbol: Symbol) -> Option<TokenKind> {
        // O(1) comparison using interned symbols
        if symbol == self.auto {
            Some(TokenKind::Auto)
        } else if symbol == self.break_ {
            Some(TokenKind::Break)
        } else if symbol == self.case {
            Some(TokenKind::Case)
        } else if symbol == self.char_ {
            Some(TokenKind::Char)
        } else if symbol == self.const_ {
            Some(TokenKind::Const)
        } else if symbol == self.continue_ {
            Some(TokenKind::Continue)
        } else if symbol == self.default {
            Some(TokenKind::Default)
        } else if symbol == self.do_ {
            Some(TokenKind::Do)
        } else if symbol == self.double {
            Some(TokenKind::Double)
        } else if symbol == self.else_ {
            Some(TokenKind::Else)
        } else if symbol == self.enum_ {
            Some(TokenKind::Enum)
        } else if symbol == self.extern_ {
            Some(TokenKind::Extern)
        } else if symbol == self.float {
            Some(TokenKind::Float)
        } else if symbol == self.for_ {
            Some(TokenKind::For)
        } else if symbol == self.goto {
            Some(TokenKind::Goto)
        } else if symbol == self.if_ {
            Some(TokenKind::If)
        } else if symbol == self.inline {
            Some(TokenKind::Inline)
        } else if symbol == self.int {
            Some(TokenKind::Int)
        } else if symbol == self.long {
            Some(TokenKind::Long)
        } else if symbol == self.register {
            Some(TokenKind::Register)
        } else if symbol == self.restrict {
            Some(TokenKind::Restrict)
        } else if symbol == self.return_ {
            Some(TokenKind::Return)
        } else if symbol == self.short {
            Some(TokenKind::Short)
        } else if symbol == self.signed {
            Some(TokenKind::Signed)
        } else if symbol == self.sizeof {
            Some(TokenKind::Sizeof)
        } else if symbol == self.static_ {
            Some(TokenKind::Static)
        } else if symbol == self.struct_ {
            Some(TokenKind::Struct)
        } else if symbol == self.switch {
            Some(TokenKind::Switch)
        } else if symbol == self.typedef {
            Some(TokenKind::Typedef)
        } else if symbol == self.union_ {
            Some(TokenKind::Union)
        } else if symbol == self.unsigned {
            Some(TokenKind::Unsigned)
        } else if symbol == self.void {
            Some(TokenKind::Void)
        } else if symbol == self.volatile {
            Some(TokenKind::Volatile)
        } else if symbol == self.while_ {
            Some(TokenKind::While)
        } else if symbol == self.alignas {
            Some(TokenKind::Alignas)
        } else if symbol == self.alignof {
            Some(TokenKind::Alignof)
        } else if symbol == self.atomic {
            Some(TokenKind::Atomic)
        } else if symbol == self.bool_ {
            Some(TokenKind::Bool)
        } else if symbol == self.complex {
            Some(TokenKind::Complex)
        } else if symbol == self.generic {
            Some(TokenKind::Generic)
        } else if symbol == self.noreturn {
            Some(TokenKind::Noreturn)
        } else if symbol == self.pragma {
            Some(TokenKind::Pragma)
        } else if symbol == self.static_assert {
            Some(TokenKind::StaticAssert)
        } else if symbol == self.thread_local {
            Some(TokenKind::ThreadLocal)
        } else {
            None
        }
    }
}

/// Lexer state machine
pub struct Lexer<'src> {
    #[allow(unused)]
    source_manager: &'src SourceManager,
    #[allow(unused)]
    diag: &'src mut DiagnosticEngine,
    #[allow(unused)]
    lang_opts: &'src LangOptions,
    #[allow(unused)]
    target_info: &'src TargetTriple,

    // Current position in token stream
    tokens: &'src [PPToken],
    current_index: usize,

    // Pre-interned keyword symbols for fast comparison
    keywords: KeywordTable,

    // Lexing state
    #[allow(unused)]
    current_token: Option<Token>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer with the given preprocessor token stream
    pub fn new(
        source_manager: &'src SourceManager,
        diag: &'src mut DiagnosticEngine,
        lang_opts: &'src LangOptions,
        target_info: &'src TargetTriple,
        tokens: &'src [PPToken],
    ) -> Self {
        let keywords = KeywordTable::new();

        Lexer {
            source_manager,
            diag,
            lang_opts,
            target_info,
            tokens,
            current_index: 0,
            keywords,
            current_token: None,
        }
    }

    /// Parse C11 integer literal syntax
    fn parse_c11_integer_literal(&self, text: Symbol) -> Result<i64, ()> {
        let text_str = text.as_str();

        // C11 integer literal format: [0[xX]][digits][suffix]
        // Suffixes: u/U (unsigned), l/L (long), ll/LL (long long)
        // Can be combined: ul, ull, etc.

        // Find where the suffix starts (if any)
        let mut end_of_digits = text_str.len();
        let mut _has_unsigned = false;
        let mut _has_long = false;
        let mut _has_long_long = false;

        // Check for suffixes (case insensitive)
        let lower_text = text_str.to_lowercase();
        if lower_text.ends_with("ull") || lower_text.ends_with("llu") {
            end_of_digits = text_str.len() - 3;
            _has_long_long = true;
            _has_unsigned = lower_text.ends_with("ull");
        } else if lower_text.ends_with("ul") || lower_text.ends_with("lu") {
            end_of_digits = text_str.len() - 2;
            _has_long = true;
            _has_unsigned = lower_text.ends_with("ul");
        } else if lower_text.ends_with("u") {
            end_of_digits = text_str.len() - 1;
            _has_unsigned = true;
        } else if lower_text.ends_with("ll") {
            end_of_digits = text_str.len() - 2;
            _has_long_long = true;
        } else if lower_text.ends_with("l") {
            end_of_digits = text_str.len() - 1;
            _has_long = true;
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
            16 => u64::from_str_radix(digits, 16),
            8 => u64::from_str_radix(digits, 8),
            10 => digits.parse::<u64>(),
            _ => unreachable!(),
        };

        match value {
            Ok(val) => Ok(val as i64), // Cast to i64, allowing wraparound for large values
            Err(_) => Err(()), // Invalid integer constant
        }
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
                if let Some(keyword) = self.keywords.is_keyword(symbol) {
                    keyword
                } else {
                    TokenKind::Identifier(symbol)
                }
            }
            PPTokenKind::StringLiteral(symbol) => TokenKind::StringLiteral(symbol),
            PPTokenKind::CharLiteral(codepoint, _) => TokenKind::CharacterConstant(codepoint),
            PPTokenKind::Number(value) => {
                // Try to parse as integer first
                match self.parse_c11_integer_literal(value) {
                    Ok(parsed_value) => TokenKind::IntegerConstant(parsed_value),
                    Err(_) => {
                        // If integer parsing fails, it might be a float
                        // For now, just pass the raw text to the parser
                        TokenKind::FloatConstant(value)
                    }
                }
            }
            PPTokenKind::Eof => TokenKind::EndOfFile,
            // Map preprocessor punctuation to lexer tokens
            PPTokenKind::Plus => TokenKind::Plus,
            PPTokenKind::Minus => TokenKind::Minus,
            PPTokenKind::Star => TokenKind::Star,
            PPTokenKind::Slash => TokenKind::Slash,
            PPTokenKind::Percent => TokenKind::Percent,
            PPTokenKind::And => TokenKind::And,
            PPTokenKind::Or => TokenKind::Or,
            PPTokenKind::Xor => TokenKind::Xor,
            PPTokenKind::Not => TokenKind::Not,
            PPTokenKind::Tilde => TokenKind::Tilde,
            PPTokenKind::Less => TokenKind::Less,
            PPTokenKind::Greater => TokenKind::Greater,
            PPTokenKind::LessEqual => TokenKind::LessEqual,
            PPTokenKind::GreaterEqual => TokenKind::GreaterEqual,
            PPTokenKind::Equal => TokenKind::Equal,
            PPTokenKind::NotEqual => TokenKind::NotEqual,
            PPTokenKind::LeftShift => TokenKind::LeftShift,
            PPTokenKind::RightShift => TokenKind::RightShift,
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
            PPTokenKind::Increment => TokenKind::Increment,
            PPTokenKind::Decrement => TokenKind::Decrement,
            PPTokenKind::Arrow => TokenKind::Arrow,
            PPTokenKind::Dot => TokenKind::Dot,
            PPTokenKind::Question => TokenKind::Question,
            PPTokenKind::Colon => TokenKind::Colon,
            PPTokenKind::Comma => TokenKind::Comma,
            PPTokenKind::Semicolon => TokenKind::Semicolon,
            PPTokenKind::LeftParen => TokenKind::LeftParen,
            PPTokenKind::RightParen => TokenKind::RightParen,
            PPTokenKind::LeftBracket => TokenKind::LeftBracket,
            PPTokenKind::RightBracket => TokenKind::RightBracket,
            PPTokenKind::LeftBrace => TokenKind::LeftBrace,
            PPTokenKind::RightBrace => TokenKind::RightBrace,
            PPTokenKind::Ellipsis => TokenKind::Ellipsis,
            PPTokenKind::LogicAnd => TokenKind::LogicAnd,
            PPTokenKind::LogicOr => TokenKind::LogicOr,
            // PPTokenKind::Defined is handled in expressions, not keywords
            PPTokenKind::Hash => TokenKind::Unknown,  // # not used in lexer
            PPTokenKind::HashHash => TokenKind::Unknown, // ## not used in lexer
            PPTokenKind::Unknown => TokenKind::Unknown,
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
            if let TokenKind::StringLiteral(current_symbol) = tokens[i].kind {
                // Start collecting string literals
                let current_str = current_symbol.as_str();
                let mut concatenated_content = String::new();
                let start_location = tokens[i].location.start;

                // Get the content of the first string literal (removing quotes)
                if current_str.starts_with('"') && current_str.ends_with('"') {
                    let content = &current_str[1..current_str.len() - 1];
                    concatenated_content.push_str(content);
                } else {
                    // Invalid string literal format, just push as-is
                    result.push(tokens[i]);
                    i += 1;
                    continue;
                }

                // Look ahead for more string literals
                let mut j = i + 1;
                while j < tokens.len() {
                    if let TokenKind::StringLiteral(next_symbol) = tokens[j].kind {
                        let next_str = next_symbol.as_str();
                        if next_str.starts_with('"') && next_str.ends_with('"') {
                            let content = &next_str[1..next_str.len() - 1];
                            concatenated_content.push_str(content);
                            j += 1;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }

                // Create properly formatted concatenated string literal
                let final_string = format!("\"{}\"", concatenated_content);
                let concatenated_symbol = Symbol::new(&final_string);
                let end_location = tokens[j - 1].location.end;
                result.push(Token {
                    kind: TokenKind::StringLiteral(concatenated_symbol),
                    location: SourceSpan {
                        start: start_location,
                        end: end_location,
                    },
                });

                i = j;
            } else {
                result.push(tokens[i]);
                i += 1;
            }
        }

        result
    }
}

#[cfg(test)]
mod tests_lexer;
