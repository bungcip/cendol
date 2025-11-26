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
    // Literals
    IntegerConstant(i64),    // Parsed integer value
    FloatConstant(Symbol),   // Raw float literal text (preserves precision)
    CharacterConstant(u32),  // Unicode codepoint
    StringLiteral(Symbol),   // Interned string literal

    // Keywords (C11)
    Auto, Break, Case, Char, Const, Continue, Default, Do, Double, Else, Enum,
    Extern, Float, For, Goto, If, Inline, Int, Long, Register, Restrict,
    Return, Short, Signed, Sizeof, Static, Struct, Switch, Typedef, Union,
    Unsigned, Void, Volatile, While,
    // C11 specific keywords
    Alignas, Alignof, Atomic, Bool, Complex, Generic, Noreturn, Pragma, StaticAssert,
    ThreadLocal,

    // Identifiers
    Identifier(Symbol), // Interned identifier

    // Operators and punctuation
    Plus, Minus, Star, Slash, Percent, // + - * / %
    And, Or, Xor, Not, Tilde, // & | ^ ! ~
    Less, Greater, LessEqual, GreaterEqual, Equal, NotEqual, // < > <= >= == !=
    LeftShift, RightShift, // << >>
    Assign, PlusAssign, MinusAssign, // = += -=
    StarAssign, DivAssign, ModAssign, // *= /= %=
    AndAssign, OrAssign, XorAssign, // &= |= ^=
    LeftShiftAssign, RightShiftAssign, // <<= >>=
    Increment, Decrement, // ++ --
    Arrow, Dot, // -> .
    Question, Colon, // ? :
    Comma, Semicolon, // , ;
    LeftParen, RightParen, // ( )
    LeftBracket, RightBracket, // [ ]
    LeftBrace, RightBrace, // { }
    Ellipsis,   // ...
    LogicAnd, LogicOr, // && ||

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

/// Table of pre-interned C11 keywords for O(1) keyword recognition
pub struct KeywordTable {
    // C11 keywords
    auto: Symbol, break_: Symbol, case: Symbol, char_: Symbol, const_: Symbol,
    continue_: Symbol, default: Symbol, do_: Symbol, double: Symbol, else_: Symbol,
    enum_: Symbol, extern_: Symbol, float: Symbol, for_: Symbol, goto: Symbol,
    if_: Symbol, inline: Symbol, int: Symbol, long: Symbol, register: Symbol,
    restrict: Symbol, return_: Symbol, short: Symbol, signed: Symbol,
    sizeof: Symbol, static_: Symbol, struct_: Symbol, switch: Symbol,
    typedef: Symbol, union_: Symbol, unsigned: Symbol, void: Symbol,
    volatile: Symbol, while_: Symbol,
    // C11 specific
    alignas: Symbol, alignof: Symbol, atomic: Symbol, bool_: Symbol,
    complex: Symbol, generic: Symbol, noreturn: Symbol, pragma: Symbol,
    static_assert: Symbol, thread_local: Symbol,
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
        if symbol == self.auto { Some(TokenKind::Auto) }
        else if symbol == self.break_ { Some(TokenKind::Break) }
        else if symbol == self.case { Some(TokenKind::Case) }
        else if symbol == self.char_ { Some(TokenKind::Char) }
        else if symbol == self.const_ { Some(TokenKind::Const) }
        else if symbol == self.continue_ { Some(TokenKind::Continue) }
        else if symbol == self.default { Some(TokenKind::Default) }
        else if symbol == self.do_ { Some(TokenKind::Do) }
        else if symbol == self.double { Some(TokenKind::Double) }
        else if symbol == self.else_ { Some(TokenKind::Else) }
        else if symbol == self.enum_ { Some(TokenKind::Enum) }
        else if symbol == self.extern_ { Some(TokenKind::Extern) }
        else if symbol == self.float { Some(TokenKind::Float) }
        else if symbol == self.for_ { Some(TokenKind::For) }
        else if symbol == self.goto { Some(TokenKind::Goto) }
        else if symbol == self.if_ { Some(TokenKind::If) }
        else if symbol == self.inline { Some(TokenKind::Inline) }
        else if symbol == self.int { Some(TokenKind::Int) }
        else if symbol == self.long { Some(TokenKind::Long) }
        else if symbol == self.register { Some(TokenKind::Register) }
        else if symbol == self.restrict { Some(TokenKind::Restrict) }
        else if symbol == self.return_ { Some(TokenKind::Return) }
        else if symbol == self.short { Some(TokenKind::Short) }
        else if symbol == self.signed { Some(TokenKind::Signed) }
        else if symbol == self.sizeof { Some(TokenKind::Sizeof) }
        else if symbol == self.static_ { Some(TokenKind::Static) }
        else if symbol == self.struct_ { Some(TokenKind::Struct) }
        else if symbol == self.switch { Some(TokenKind::Switch) }
        else if symbol == self.typedef { Some(TokenKind::Typedef) }
        else if symbol == self.union_ { Some(TokenKind::Union) }
        else if symbol == self.unsigned { Some(TokenKind::Unsigned) }
        else if symbol == self.void { Some(TokenKind::Void) }
        else if symbol == self.volatile { Some(TokenKind::Volatile) }
        else if symbol == self.while_ { Some(TokenKind::While) }
        else if symbol == self.alignas { Some(TokenKind::Alignas) }
        else if symbol == self.alignof { Some(TokenKind::Alignof) }
        else if symbol == self.atomic { Some(TokenKind::Atomic) }
        else if symbol == self.bool_ { Some(TokenKind::Bool) }
        else if symbol == self.complex { Some(TokenKind::Complex) }
        else if symbol == self.generic { Some(TokenKind::Generic) }
        else if symbol == self.noreturn { Some(TokenKind::Noreturn) }
        else if symbol == self.pragma { Some(TokenKind::Pragma) }
        else if symbol == self.static_assert { Some(TokenKind::StaticAssert) }
        else if symbol == self.thread_local { Some(TokenKind::ThreadLocal) }
        else { None }
    }
}
```

### Processing Algorithm

The lexer operates on the PPToken stream from the preprocessor with pre-interned keywords for efficient recognition:

1. **Initialization**:
   - Create `KeywordTable` with all C11 keywords pre-interned using `Symbol::new()`
   - Set up lexer with PPToken stream reference

2. **Token Stream Iteration**:
   - Process each PPToken in sequence from the preprocessor output
   - Convert PPTokenKind to corresponding TokenKind
   - Preserve source location information

3. **Token Classification**:
   - **Keywords**: For PPTokenKind::Identifier(symbol), check `keywords.is_keyword(symbol)` for O(1) keyword recognition
   - **Identifiers**: Convert PPTokenKind::Identifier(Symbol) directly to TokenKind::Identifier(Symbol) if not a keyword
   - **Literals**: Transform preprocessed literals to parsed values:
     - PPTokenKind::Number(value) → TokenKind::IntegerConstant(i64) after C11 integer parsing
     - PPTokenKind::CharLiteral(codepoint) → TokenKind::CharacterConstant(u32)
     - PPTokenKind::StringLiteral(symbol) → TokenKind::StringLiteral(Symbol)
     - Float literals preserve raw text as Symbol for precision
   - **Operators/Punctuation**: Direct mapping from PPTokenKind to TokenKind

4. **String Literal Concatenation**:
   - Adjacent string literals are merged according to C11 6.4.5
   - Quotes are removed and contents concatenated
   - Result stored as single TokenKind::StringLiteral

5. **Integer Literal Parsing**:
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
- **Efficient Literal Handling**: C11-compliant integer and float literal parsing
- **String Literal Concatenation**: Automatic merging of adjacent string literals
- **Unified Source Location**: Maintains accurate location tracking from preprocessor
- **Error Recovery**: Continues lexing after encountering invalid input
- **UTF-8 Only**: Assumes UTF-8 input (handled by preprocessor)
- **No Trigraph/Digraph Support**: Consistent with preprocessor design
- **Global Symbol Interning**: Uses `symbol_table` crate for efficient string interning