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

1. **Character-by-character processing** with lookahead for efficiency
2. **Two-pass macro expansion**: 
   - First pass: Collect macro definitions
   - Second pass: Expand macro references
3. **Include file caching** with path resolution
4. **Recursive include guards** detection to prevent infinite loops

### Key Features

- **Variadic macro support** (C99/C11)
- **_Pragma operator** in expressions
- **Empty macro argument** handling
- **Stringification and charification** operators
- **__DATE__, __TIME__, __FILE__, __LINE__** expansion
- **Feature test macro** support for conditional feature enabling