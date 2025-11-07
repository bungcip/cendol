## Lexer Phase

### Overview

The lexer processes the token stream produced by the preprocessor and converts it into a sequence of lexical tokens that represent the syntactic elements of the C11 language. It operates on the preprocessed source, recognizing keywords, operators, literals, and identifiers while maintaining source location information for error reporting.

### Responsibilities

- **Token Stream Processing**: Convert preprocessor tokens (PPToken) into lexical tokens (Token)
- **Keyword Recognition**: Identify and classify C11 keywords
- **Literal Processing**: Parse and validate numeric, character, and string literals
- **Operator Recognition**: Handle all C11 operators and punctuation
- **Comment Elimination**: Skip comments (already handled by preprocessor)
- **Error Recovery**: Continue lexing after encountering invalid tokens

### Data Structures

```rust
/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Literals
    IntegerConstant(i64),    // Parsed integer value
    FloatConstant(f64),      // Parsed float value
    CharacterConstant(u32),  // Unicode codepoint
    StringLiteral(Symbol),   // Interned string literal

    // Keywords (C11)
    Auto, Break, Case, Char, Const, Continue, Default, Do, Double, Else, Enum,
    Extern, Float, For, Goto, If, Inline, Int, Long, Register, Restrict,
    Return, Short, Signed, Sizeof, Static, Struct, Switch, Typedef, Union,
    Unsigned, Void, Volatile, While,
    // C11 specific keywords
    Alignas, Alignof, Atomic, Bool, Complex, Generic, Noreturn, StaticAssert,
    ThreadLocal,

    // Identifiers
    Identifier(Symbol),      // Interned identifier

    // Operators and punctuation
    Plus, Minus, Star, Slash, Percent, // + - * / %
    And, Or, Xor, Not, // & | ^ !
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
    Ellipsis, // ...

    // Special tokens
    EndOfFile,
    Unknown,
}

/// Token with source location for the parser
#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub location: SourceSpan,
}

/// Lexer state machine
pub struct Lexer<'src> {
    source_manager: &'src SourceManager,
    diag: &'src DiagnosticEngine,
    lang_opts: &'src LangOptions,
    target_info: &'src TargetTriple,

    // Current position in token stream
    tokens: &'src [PPToken],
    current_index: usize,

    // Pre-interned keyword symbols for fast comparison
    keywords: KeywordTable,

    // Lexing state
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
    complex: Symbol, generic: Symbol, noreturn: Symbol, static_assert: Symbol,
    thread_local: Symbol,
}

impl KeywordTable {
    pub fn new(string_interner: &mut StringInterner) -> Self {
        KeywordTable {
            auto: string_interner.get_or_intern("auto"),
            break_: string_interner.get_or_intern("break"),
            case: string_interner.get_or_intern("case"),
            // ... initialize all keywords
            thread_local: string_interner.get_or_intern("_Thread_local"),
        }
    }

    pub fn is_keyword(&self, symbol: Symbol) -> Option<TokenKind> {
        // O(1) comparison using interned symbols
        if symbol == self.auto { Some(TokenKind::Auto) }
        else if symbol == self.break_ { Some(TokenKind::Break) }
        // ... check all keywords
        else { None }
    }
}
```

### Processing Algorithm

The lexer operates on the PPToken stream from the preprocessor with pre-interned keywords for efficient recognition:

1. **Initialization**:
   - Create `KeywordTable` with all C11 keywords pre-interned using `StringInterner`
   - Set up lexer with PPToken stream reference

2. **Token Stream Iteration**:
   - Process each PPToken in sequence from the preprocessor output
   - Convert PPTokenKind to corresponding TokenKind
   - Preserve source location information

3. **Token Classification**:
   - **Keywords**: For PPTokenKind::Identifier(symbol), check `keywords.is_keyword(symbol)` for O(1) keyword recognition
   - **Identifiers**: Convert PPTokenKind::Identifier(Symbol) directly to TokenKind::Identifier(Symbol) if not a keyword
   - **Literals**: Transform preprocessed literals to parsed values:
     - PPTokenKind::Number(i64) → TokenKind::IntegerConstant(i64)
     - PPTokenKind::CharLiteral(u32) → TokenKind::CharacterConstant(u32)
     - PPTokenKind::StringLiteral(Symbol) → TokenKind::StringLiteral(Symbol)
   - **Operators/Punctuation**: Direct mapping from PPTokenKind to TokenKind

4. **Error Handling**:
   - Invalid tokens generate diagnostic messages
   - Continue processing for error recovery
   - Unknown tokens mapped to TokenKind::Unknown

### Key Features

- **Stream-based Processing**: Operates on preprocessor output rather than raw source
- **Zero-copy Tokenization**: Reuses preprocessor token data where possible
- **Efficient Literal Handling**: Leverages preprocessor's parsed literal values
- **Unified Source Location**: Maintains accurate location tracking from preprocessor
- **Error Recovery**: Continues lexing after encountering invalid input
- **UTF-8 Only**: Assumes UTF-8 input (handled by preprocessor)
- **No Trigraph/Digraph Support**: Consistent with preprocessor design