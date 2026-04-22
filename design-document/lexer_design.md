# Lexer Design

## Overview

The lexer (or tokenizer) transforms a stream of preprocessing tokens into a stream of lexical tokens. It classifies identifiers, keywords, literals, and operators according to the C23 standard.

## Responsibilities

1. **Token Conversion**: Map `PPToken` (from the preprocessor) to `Token`.
2. **Keyword Recognition**: Identify interned identifiers that match C23 keywords.
3. **Literal Parsing**: Parse the raw source text of numeric and character literals into their representation format (e.g., `i64` for integers).
4. **String Concatenation**: Automatically merge adjacent string literals as required by Phase 6 of C translation.

## Token Representation

Each `Token` consists of:
- `TokenKind`: The category (e.g., `Ident`, `Plus`, `IntegerConstant`).
- `SourceLoc`: The primary location of the token.
- `SourceSpan`: The full span of the token.

## Implementation Details

### Optimized Keyword Lookup
Given the high frequency of identifiers, keywords are identified using a pre-populated hash map of interned `NameId`s.

### Integer Literals (C23 Support)
The lexer supports the expanded C23 integer literal grammar:
- **Bases**: Decimal, Hexadecimal, Octal, and **Binary** (`0b...`).
- **Separators**: Digit separators (`'`) are filtered during parsing.
- **Suffixes**: Includes support for standard suffixes (`u`, `l`, `ll`) and new C23 suffixes (`wb`, `uwb` for bit-precise integers).

### Floating-Point Literals
Supports decimal and hexadecimal floating-point formats, including E/P notation and `f`, `l`, `d` suffixes.

### String Literals
Handles standard strings, `u8`, `u`, `U`, and `L` prefixed literals. Concatenation occurs before the parser sees the tokens, ensuring that ` "hello" "world" ` is treated as a single `"helloworld"` token.

## Lexer State Machine

The lexer is implemented as a simple iterator-based converter. Because the preprocessor already handles the heavy lifting of reading bytes and identifying tokens, the lexical phase is extremely fast and mostly involves classification and literal conversion.