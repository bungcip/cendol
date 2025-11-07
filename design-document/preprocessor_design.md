## Preprocessor Phase

### Responsibilities
- Macro expansion and substitution
- Header file inclusion (system and user headers)
- Conditional compilation (#ifdef, #ifndef, #if, #else, #elif, #endif)
- Line control (#line)
- Pragma directive handling
- _Pragma operator support
- Feature test macros (_POSIX_C_SOURCE, _GNU_SOURCE, etc.)

### Data Structures

```rust
/// Preprocessor context
pub struct Preprocessor<'src> {
    source: &'src str,
    current_pos: usize,
    current_line: u32,
    current_col: u32,
    current_file: SourceId,
    
    // Macro management
    macro_table: HashMap<Symbol, MacroDef>,
    include_paths: Vec<PathBuf>,
    system_include_paths: Vec<PathBuf>,
    
    // Conditional compilation state
    conditional_stack: Vec<ConditionalContext>,
    current_condition_state: ConditionState,
    
    // _Pragma support
    pending_pragma_directives: Vec<PragmaDirective>,
}

/// Macro definition structure
pub struct MacroDef {
    pub name: Symbol,
    pub is_function_like: bool,
    pub parameters: Option<Vec<Symbol>>, // For function-like macros
    pub replacement_list: Vec<ReplacementToken>,
    pub is_variadic: bool,
    pub variadic_parameter: Option<Symbol>, // __VA_ARGS__
    pub location: SourceSpan,
    pub is_poisoned: bool, // #undef or #pragma GCC poison
}

/// Token after macro expansion
#[derive(Debug, Clone)]
pub struct ReplacementToken {
    pub kind: TokenKind,
    pub value: Symbol, // For literals and identifiers
    pub source_span: SourceSpan,
    pub is_stringizing: bool, // # operator
    pub is_charizing: bool, // ## operator context
}

/// Conditional compilation state
#[derive(Debug, Clone)]
struct ConditionalContext {
    kind: ConditionalKind, // If, Ifdef, Ifndef
    // For #if expressions
    expression: Option<ConstantExpression>,
    // For #ifdef/#ifndef
    macro_name: Option<Symbol>,
    // Was this branch taken?
    branch_taken: bool,
    // Nested conditionals
    nested_taken: bool,
}
```

### Processing Algorithm

The preprocessor will implement a robust macro expansion algorithm, aiming for behavior consistent with Clang's preprocessor, which closely adheres to the C standard.

1.  **Tokenization**: The input stream is tokenized into preprocessing tokens. This includes handling whitespace, comments, and string literal concatenation.
2.  **Macro Definition Collection**:
    -   When `#define` is encountered, the macro name, parameters (if function-like), and replacement list are stored in the `macro_table`.
    -   Macros are marked as "defined" or "undefined" (`#undef`).
    -   Special handling for `__VA_ARGS__` and variadic macros.
3.  **Macro Expansion (Iterative Scan and Rescan)**:
    -   When an identifier is encountered, the preprocessor checks if it's a defined macro.
    -   If it is a macro, it's replaced by its replacement list.
    -   **Argument Pre-scan**: For function-like macros, arguments are fully macro-expanded *before* substitution into the replacement list. This is a critical step for correct behavior (e.g., `FOO(BAR)` where `BAR` is also a macro).
    -   **Stringification (`#`)**: If the `#` operator is used in a function-like macro, the corresponding argument is converted to a string literal *before* any macro expansion of the argument itself.
    -   **Token Pasting (`##`)**: If `##` is used, the tokens on either side are concatenated to form a new token, which is then rescanned for further macro expansion.
    -   **Rescan and Further Replacement**: After a macro is expanded, the resulting tokens are immediately rescanned for further macro expansions. This process continues until no more macros can be expanded in the current token sequence.
    -   **Macro Blacklist/Protection**: To prevent infinite recursion, a macro name is temporarily "blacklisted" (marked as non-expandable) during its own expansion. This ensures that a macro does not expand to itself directly or indirectly.
4.  **Include File Handling**:
    -   `#include` directives are processed by locating the specified file (using include paths).
    -   The content of the included file is recursively preprocessed and inserted into the token stream.
    -   Include guards (`#ifndef`/`#define`/`#endif`) are detected to prevent multiple inclusions of the same header.
5.  **Conditional Compilation**:
    -   `#if`, `#ifdef`, `#ifndef`, `#elif`, `#else`, `#endif` directives control which parts of the source code are processed.
    -   Expressions in `#if` and `#elif` are evaluated as constant expressions. `defined` operator is handled here.
6.  **Line Control**: `#line` directives update the current source file and line number information.
7.  **Pragma Directives**: `#pragma` directives are parsed and handled (e.g., `_Pragma` operator).

### Key Features

### Key Features

- **Variadic macro support** (C99/C11)
- **_Pragma operator** in expressions
- **Empty macro argument** handling
- **Stringification and charification** operators
- **__DATE__, __TIME__, __FILE__, __LINE__** expansion
- **Feature test macro** support for conditional feature enabling
- **No Trigraph or Digraph Support**: For simplicity and modern C usage, trigraphs and digraphs will not be supported.
- **UTF-8 Only**: The preprocessor will assume and only support UTF-8 encoded source files.