# Lexer Design

## Overview

The lexer (or tokenizer) converts a preprocessor token stream into a lexical token stream. It recognizes keywords, identifiers, literals, operators, and punctuation according to C11 lexical rules, and performs string literal concatenation as required by the C11 standard.

## Key Responsibilities

- **Token Conversion**: Convert preprocessing tokens (`PPToken`) to lexical tokens (`Token`)
- **Keyword Recognition**: Identify C11 keywords using optimized symbol table lookup
- **Literal Parsing**: Parse integer, float, character, and string literals with C11 syntax support
- **String Literal Concatenation**: Perform string literal concatenation as per C11 6.4.5
- **Token Classification**: Classify preprocessing tokens into appropriate lexical categories
- **Source Location Tracking**: Maintain accurate source location information

## Token Types

The lexer produces various token types including:

### Literals
- `IntegerConstant(i64)`: Parsed integer literal value with C11 suffix support
- `FloatConstant(f64)`: Parsed float literal value with C11 format support
- `CharacterConstant(u8)`: Byte value of character constant
- `StringLiteral(StringId)`: Interned string literal with quotes removed

### Identifiers
- `Identifier(StringId)`: Interned identifier name

### Keywords (Storage Class Specifiers)
- `Auto`, `Extern`, `Register`, `Static`, `ThreadLocal`

### Keywords (Type Qualifiers)
- `Const`, `Restrict`, `Volatile`, `Atomic`

### Keywords (Type Specifiers)
- `Bool`, `Char`, `Double`, `Float`, `Int`, `Long`, `Short`, `Signed`, `Unsigned`, `Void`, `Complex`

### Keywords (Control Flow)
- `Break`, `Case`, `Continue`, `Default`, `Do`, `Else`, `For`, `Goto`, `If`, `Return`, `Switch`, `While`

### Keywords (Other)
- `Alignas`, `Alignof`, `Generic`, `Inline`, `Noreturn`, `Pragma`, `Sizeof`, `StaticAssert`, `Typedef`, `Attribute`

### Operators (Arithmetic)
- `Plus`, `Minus`, `Star`, `Slash`, `Percent`, `Increment`, `Decrement`

### Operators (Bitwise)
- `And`, `Or`, `Xor`, `Not`, `Tilde`, `LeftShift`, `RightShift`

### Operators (Comparison)
- `Less`, `Greater`, `LessEqual`, `GreaterEqual`, `Equal`, `NotEqual`

### Operators (Assignment)
- `Assign`, `PlusAssign`, `MinusAssign`, `StarAssign`, `DivAssign`, `ModAssign`, `AndAssign`, `OrAssign`, `XorAssign`, `LeftShiftAssign`, `RightShiftAssign`

### Operators (Logical)
- `LogicAnd`, `LogicOr`

### Punctuation
- `Arrow`, `Dot`, `Question`, `Colon`, `Comma`, `Semicolon`, `Ellipsis`
- Brackets: `LeftParen`, `RightParen`, `LeftBracket`, `RightBracket`, `LeftBrace`, `RightBrace`

## Implementation Details

### Optimized Keyword Recognition

The lexer uses a pre-initialized hash map for keyword recognition, providing O(1) lookup performance:

```rust
fn is_keyword(symbol: StringId) -> Option<TokenKind> {
    keyword_map().get(&symbol).copied()
}

fn keyword_map() -> &'static hashbrown::HashMap<StringId, TokenKind> {
    // Pre-populated map of all C11 keywords
}
```

### Integer Literal Parsing

Optimized integer parsing that handles C11 format including:
- Decimal, octal, and hexadecimal formats
- Various suffixes (u, l, ll, ul, ull, etc.)
- Proper base detection and validation

### Float Literal Parsing

Comprehensive float parsing supporting:
- Decimal and hexadecimal floating-point literals (C99/C11)
- Scientific notation (e.g., 1.23e-4)
- Various suffixes (f, F, l, L)
- Hexadecimal float format (0x1.2p3)

### String Literal Concatenation

The lexer implements C11-compliant string literal concatenation (6.4.5) by:
- Detecting adjacent string literals in the token stream
- Concatenating their content in a single pass
- Creating a single token representing the concatenated string

### Performance Optimizations

- **Symbol Interning**: All identifiers and string literals use interned strings for memory efficiency and fast comparison
- **Optimized Suffix Stripping**: Fast integer/float suffix removal using byte-level operations
- **Match-based Classification**: Optimized punctuation token classification using match statements
- **Contiguous Processing**: Efficient processing of token streams without unnecessary allocations

## Input/Output Interface

The lexer takes a slice of preprocessing tokens (`&[PPToken]`) and produces a vector of lexical tokens (`Vec<Token>`), maintaining source location information throughout the conversion process.