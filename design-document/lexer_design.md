## Lexer Phase

### Overview

The lexer processes the token stream produced by the preprocessor and converts it into a sequence of lexical tokens that represent the syntactic elements of the C11 language. It operates on the preprocessed source, recognizing keywords, operators, literals, and identifiers while maintaining source location information for error reporting.

### Responsibilities

- **Token Stream Processing**: Convert preprocessor tokens (PPToken) into lexical tokens (Token)
- **Keyword Recognition**: Identify and classify C11 keywords using pre-interned symbol table
- **Literal Processing**: Parse and validate numeric, character, and string literals
- **Operator Recognition**: Handle all C11 operators and punctuation
- **String Literal Concatenation**: Merge adjacent string literals (C11 6.4.5)
- **Error Recovery**: Continue lexing after encountering invalid tokens

### Data Structures

```rust
/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // === LITERALS ===
    IntegerConstant(i64),   // Parsed integer literal value
    FloatConstant(Symbol),  // Raw float literal text
    CharacterConstant(u8),  // Byte value of character constant
    StringLiteral(Symbol),  // Interned string literal

    // === IDENTIFIERS ===
    Identifier(Symbol), // Interned identifier

    // === KEYWORDS ===
    // Storage class specifiers
    Auto, Extern, Register, Static, ThreadLocal,

    // Type qualifiers
    Const, Restrict, Volatile, Atomic,

    // Type specifiers
    Bool, Char, Double, Float, Int, Long, Short, Signed, Unsigned, Void, Complex,

    // Complex type specifiers
    Struct, Union, Enum,

    // Control flow
    Break, Case, Continue, Default, Do, Else, For, Goto, If, Return, Switch, While,

    // Other keywords
    Alignas, Alignof, Generic, Inline, Noreturn, Pragma, Sizeof, StaticAssert, Typedef,

    // === OPERATORS ===
    // Arithmetic operators
    Plus, Minus, Star, Slash, Percent, Increment, Decrement,

    // Bitwise operators
    And, Or, Xor, Not, Tilde, LeftShift, RightShift,

    // Comparison operators
    Less, Greater, LessEqual, GreaterEqual, Equal, NotEqual,

    // Assignment operators
    Assign, PlusAssign, MinusAssign, StarAssign, DivAssign, ModAssign,
    AndAssign, OrAssign, XorAssign, LeftShiftAssign, RightShiftAssign,

    // Logical operators
    LogicAnd, LogicOr,

    // Member access
    Arrow, Dot,

    // Ternary operator
    Question, Colon,

    // === PUNCTUATION ===
    Comma, Semicolon, Ellipsis,

    // Brackets and parentheses
    LeftParen, RightParen, LeftBracket, RightBracket, LeftBrace, RightBrace,

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

    // Lexing state
    #[allow(unused)]
    current_token: Option<Token>,
}

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
```

### Processing Algorithm

The lexer operates on the PPToken stream from the preprocessor using static lookup tables for efficient recognition:

1. **Initialization**:
   - Static `KEYWORDS` HashMap initialized lazily with `OnceLock` containing all C11 keywords
   - Static `PUNCTUATION_MAP` HashMap for systematic operator/punctuation mapping
   - Set up lexer with PPToken stream reference

2. **Token Stream Iteration**:
   - Process each PPToken in sequence from the preprocessor output
   - Convert PPTokenKind to corresponding TokenKind using lookup tables
   - Preserve source location information

3. **Token Classification**:
   - **Keywords**: For PPTokenKind::Identifier(symbol), check `is_keyword(symbol)` using static HashMap for O(1) lookup
   - **Identifiers**: Convert PPTokenKind::Identifier(Symbol) directly to TokenKind::Identifier(Symbol) if not a keyword
   - **Literals**: Transform preprocessed literals to parsed values:
     - PPTokenKind::Number(value) → TokenKind::IntegerConstant(i64) after C11 integer parsing
     - PPTokenKind::CharLiteral(codepoint) → TokenKind::CharacterConstant(u8)
     - PPTokenKind::StringLiteral(symbol) → TokenKind::StringLiteral(Symbol)
     - Float literals preserve raw text as Symbol for precision
   - **Operators/Punctuation**: Systematic mapping using static `PUNCTUATION_MAP` HashMap

4. **String Literal Concatenation**:
   - Adjacent string literals are merged according to C11 6.4.5
   - Uses `concatenate_from_position()` and `extract_string_content()` utility functions
   - Quotes are removed and contents concatenated
   - Result stored as single TokenKind::StringLiteral

5. **Integer Literal Parsing**:
   - Modular parsing using utility functions:
     - `extract_digits_and_base()` - handles base detection and suffix removal
     - `strip_integer_suffix()` - removes type suffixes (u/U, l/L, ll/LL)
     - `parse_integer_value()` - performs the actual numeric parsing
   - Supports C11 integer literal syntax with suffixes (u/U, l/L, ll/LL)
   - Handles decimal (10), octal (0...), hexadecimal (0x...) bases
   - Parses suffixes for unsigned, long, long long combinations

6. **Error Handling**:
   - Invalid tokens generate diagnostic messages
   - Continue processing for error recovery
   - Unknown tokens mapped to TokenKind::Unknown

### Key Features

- **Stream-based Processing**: Operates on preprocessor output rather than raw source
- **Zero-copy Tokenization**: Reuses preprocessor token data where possible
- **Efficient Keyword Recognition**: O(1) keyword lookup using static HashMap with lazy initialization
- **Systematic Token Classification**: Organized TokenKind enum with clear grouping and punctuation mapping table
- **Modular Parsing Logic**: Complex parsing broken into focused utility functions for maintainability
- **Efficient Literal Handling**: C11-compliant integer and float literal parsing with utility functions
- **String Literal Concatenation**: Automatic merging of adjacent string literals with refactored logic
- **Unified Source Location**: Maintains accurate location tracking from preprocessor
- **Error Recovery**: Continues lexing after encountering invalid input
- **UTF-8 Only**: Assumes UTF-8 input (handled by preprocessor)
- **No Trigraph/Digraph Support**: Consistent with preprocessor design
- **Global Symbol Interning**: Uses `symbol_table` crate for efficient string interning
- **Comprehensive Testing**: Includes tests for string literal concatenation and all token types