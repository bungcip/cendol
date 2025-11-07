## Lexer Phase

### Responsibilities
- Tokenization of preprocessed C11 source
- Recognition of all C11 keywords and operators
- Character constant and string literal processing
- Number literal parsing (integer, floating-point, suffixes)
- Comment handling (both /* */ and // styles)
- Source location tracking for error reporting

### Token Design

```rust
/// C11 token kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Literals
    IntegerConstant,
    FloatConstant,
    CharacterConstant,
    StringLiteral,
    
    // Keywords (C11)
    Auto, Break, Case, Char, Const, Continue, Default, Do, Double, Else, Enum, 
    Extern, Float, For, Goto, If, Inline, Int, Long, Register, Restrict, 
    Return, Short, Signed, Sizeof, Static, Struct, Switch, Typedef, Union, 
    Unsigned, Void, Volatile, While,
    // C11 specific keywords
    Alignas, Alignof, Atomic, Bool, Complex, Generic, Noreturn, StaticAssert, 
    ThreadLocal,
    
    // Identifiers
    Identifier,
    
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
    
    // Preprocessor directives (handled in lexing for direct inclusion)
    Hash, HashHash, // # ##
    
    // Special tokens
    EndOfFile,
    Unknown,
}

/// Token with source location
#[derive(Debug, Clone, Copy)]
pub struct Token<'src> {
    pub kind: TokenKind,
    pub text: &'src str, // Zero-copy reference to source
    pub symbol: Option<Symbol>, // For identifiers and literals
    pub location: SourceSpan,
}
```

### Lexing Algorithm

1. **State machine** with efficient transitions
2. **Longest match** principle for operator recognition
3. **UTF-8 support** with multibyte character handling
4. **Hexadecimal escape sequences** in string literals
5. **Universal character names** (\uXXXX, \UXXXXXXXX)

### Key Features

- **Raw string literals** (C11 r"..." syntax)
- **Unicode support** with source character encoding detection
- **Integer literal suffixes** (u, U, l, L, ll, LL)
- **Floating-point literal suffixes** (f, F, l, L)
- **Character encoding** support (UTF-8, UTF-16, wide chars)
- **No Trigraph or Digraph Support**: For simplicity and modern C usage, trigraphs and digraphs will not be supported.
- **UTF-8 Only**: The lexer will assume and only support UTF-8 encoded source files.
- **Memory prefetching hints**: Implemented for performance optimization in string interning.
- **SIMD considerations**: Architecture-specific SIMD intrinsics included for future batch operations.