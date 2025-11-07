# C11 Compiler Design Document

## Table of Contents
1. [Overview](#overview)
2. [Architecture Overview](#architecture-overview)
3. [Preprocessor Phase](#preprocessor-phase)
4. [Lexer Phase](#lexer-phase)
5. [Parser Phase](#parser-phase)
6. [Semantic Analysis Phase](#semantic-analysis-phase)
7. [AST Dumper Phase](#ast-dumper-phase)
8. [Data Flow and Integration](#data-flow-and-integration)
9. [Performance Considerations](#performance-considerations)
10. [Error Handling Strategy](#error-handling-strategy)

## Overview

This document outlines the design for a high-performance C11 compiler written in Rust. The compiler follows a traditional multi-phase architecture optimized for performance, cache efficiency, and comprehensive C11 standard compliance.

### Design Goals
- **Performance**: Minimize memory allocations and maximize cache locality
- **Standards Compliance**: Full C11 support including all optional features
- **Modularity**: Clear separation of concerns between phases
- **Extensibility**: Easy to extend for future C standards and optimizations
- **Debuggability**: Comprehensive error reporting and debugging support

## Architecture Overview

```
Source Code (.c files)
    ↓
[Preprocessor] → Preprocessed Source
    ↓
[Lexer] → Token Stream
    ↓
[Parser] → AST
    ↓
[Semantic Analysis] → Annotated AST
    ↓
[AST Dumper] → Output (debug/logging)
```

### Key Design Decisions

1. **Arena Allocation**: All AST nodes allocated in arena for cache locality
2. **Symbol Interning**: String deduplication using integer IDs
3. **Source Location Tracking**: Packed source location for efficient span management
4. **Zero-Copy Parsing**: Minimize intermediate allocations
5. **Streaming Processing**: Process data in chunks to reduce memory pressure

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
- **Trigraph and digraph** support (legacy compatibility)

## Parser Phase

### Responsibilities
- Build AST from token stream using Pratt parser for expressions
- Handle C11 statements, declarations, and type system
- Error recovery for graceful failure handling
- Support all C11 syntax including _Generic, compound literals, etc.

### Pratt Parser Design

```rust
/// Pratt parser context
pub struct Parser<'arena, 'src> {
    tokens: &'src [Token<'src>],
    current_idx: usize,
    arena: &'arena Arena,
    
    // Declaration parsing state
    declaration_context: DeclarationContext,
    struct_union_context: StructUnionContext,
    enum_context: Option<EnumContext>,
    
    // Function parameter context
    function_context: Option<FunctionContext>,
    
    // Error recovery
    error_recovery_stack: Vec<ErrorRecoveryPoint>,
    synchronized_tokens: HashSet<TokenKind>,
}

/// Binding power system for C operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindingPower(pub u8);

impl BindingPower {
    pub const MIN: Self = Self(10);
    pub const COMMA: Self = Self(20);
    pub const ASSIGN: Self = Self(30);
    pub const TERNARY: Self = Self(40);
    pub const LOGICAL_OR: Self = Self(50);
    pub const LOGICAL_AND: Self = Self(60);
    pub const BITWISE_OR: Self = Self(70);
    pub const BITWISE_XOR: Self = Self(80);
    pub const BITWISE_AND: Self = Self(90);
    pub const EQUALITY: Self = Self(100);
    pub const RELATIONAL: Self = Self(110);
    pub const SHIFT: Self = Self(120);
    pub const ADDITIVE: Self = Self(130);
    pub const MULTIPLICATIVE: Self = Self(140);
    pub const CAST: Self = Self(150);
    pub const UNARY: Self = Self(160);
    pub const POSTFIX: Self = Self(170);
    pub const PRIMARY: Self = Self(180);
}

/// C operator binding powers according to C standard
pub static OPERATOR_PRECEDENCE: &[(TokenKind, BindingPower)] = &[
    (TokenKind::Ellipsis, BindingPower::COMMA),
    (TokenKind::Assign, BindingPower::ASSIGN),
    (TokenKind::PlusAssign, BindingPower::ASSIGN),
    (TokenKind::MinusAssign, BindingPower::ASSIGN),
    (TokenKind::StarAssign, BindingPower::ASSIGN),
    (TokenKind::DivAssign, BindingPower::ASSIGN),
    (TokenKind::ModAssign, BindingPower::ASSIGN),
    (TokenKind::AndAssign, BindingPower::ASSIGN),
    (TokenKind::OrAssign, BindingPower::ASSIGN),
    (TokenKind::XorAssign, BindingPower::ASSIGN),
    (TokenKind::LeftShiftAssign, BindingPower::ASSIGN),
    (TokenKind::RightShiftAssign, BindingPower::ASSIGN),
    
    (TokenKind::Question, BindingPower::TERNARY),
    (TokenKind::Colon, BindingPower::TERNARY),
    
    (TokenKind::LogicOr, BindingPower::LOGICAL_OR),
    (TokenKind::LogicAnd, BindingPower::LOGICAL_AND),
    (TokenKind::Or, BindingPower::BITWISE_OR),
    (TokenKind::Xor, BindingPower::BITWISE_XOR),
    (TokenKind::And, BindingPower::BITWISE_AND),
    (TokenKind::Equal, BindingPower::EQUALITY),
    (TokenKind::NotEqual, BindingPower::EQUALITY),
    (TokenKind::Less, BindingPower::RELATIONAL),
    (TokenKind::Greater, BindingPower::RELATIONAL),
    (TokenKind::LessEqual, BindingPower::RELATIONAL),
    (TokenKind::GreaterEqual, BindingPower::RELATIONAL),
    (TokenKind::LeftShift, BindingPower::SHIFT),
    (TokenKind::RightShift, BindingPower::SHIFT),
    (TokenKind::Plus, BindingPower::ADDITIVE),
    (TokenKind::Minus, BindingPower::ADDITIVE),
    (TokenKind::Star, BindingPower::MULTIPLICATIVE),
    (TokenKind::Slash, BindingPower::MULTIPLICATIVE),
    (TokenKind::Percent, BindingPower::MULTIPLICATIVE),
];
```

### Expression Parsing (Pratt Parser)

```rust
/// Expression parser with Pratt algorithm
pub struct ExpressionParser<'arena, 'src> {
    parser: &'arena mut Parser<'arena, 'src>,
    min_binding_power: BindingPower,
}

/// Pratt parser result
pub enum ParseExprResult<'arena> {
    /// Successful expression parse
    Expression(&'arena Node<'arena>),
    /// Incomplete expression (e.g., just identifier in declaration context)
    Incomplete(Token<'src>),
    /// No expression (e.g., semicolon)
    Empty,
}

/// Nud (null denotation) function for prefix operators
type NudFn<'arena, 'src> = fn(
    parser: &mut Parser<'arena, 'src>,
    token: Token<'src>,
    binding_power: BindingPower,
) -> Result<NodeKind<'arena>, ParseError>;

/// Led (left denotation) function for infix/postfix operators
type LedFn<'arena, 'src> = fn(
    parser: &mut Parser<'arena, 'src>,
    left: &'arena Node<'arena>,
    token: Token<'src>,
    binding_power: BindingPower,
) -> Result<NodeKind<'arena>, ParseError>;

/// Pratt parser table mapping token kinds to parsing functions
pub struct PrattTable<'arena, 'src> {
    nud_functions: HashMap<TokenKind, NudFn<'arena, 'src>>,
    led_functions: HashMap<TokenKind, LedFn<'arena, 'src>>,
    binding_powers: HashMap<TokenKind, BindingPower>,
}

impl<'arena, 'src> PrattTable<'arena, 'src> {
    pub fn new() -> Self {
        Self {
            nud_functions: Self::init_nud_functions(),
            led_functions: Self::init_led_functions(),
            binding_powers: Self::init_binding_powers(),
        }
    }
    
    fn init_nud_functions() -> HashMap<TokenKind, NudFn<'arena, 'src>> {
        let mut table = HashMap::new();
        table.insert(TokenKind::Identifier, Self::nud_identifier);
        table.insert(TokenKind::IntegerConstant, Self::nud_literal);
        table.insert(TokenKind::FloatConstant, Self::nud_literal);
        table.insert(TokenKind::CharacterConstant, Self::nud_literal);
        table.insert(TokenKind::StringLiteral, Self::nud_literal);
        table.insert(TokenKind::LeftParen, Self::nud_paren_expr);
        table.insert(TokenKind::Sizeof, Self::nud_sizeof);
        table.insert(TokenKind::Alignof, Self::nud_alignof);
        table.insert(TokenKind::Generic, Self::nud_generic);
        // Unary operators
        table.insert(TokenKind::Plus, Self::nud_unary_op);
        table.insert(TokenKind::Minus, Self::nud_unary_op);
        table.insert(TokenKind::Star, Self::nud_unary_op);
        table.insert(TokenKind::And, Self::nud_unary_op);
        table.insert(TokenKind::Not, Self::nud_unary_op);
        table.insert(TokenKind::BitNot, Self::nud_unary_op);
        table.insert(TokenKind::Increment, Self::nud_unary_op);
        table.insert(TokenKind::Decrement, Self::nud_unary_op);
        table
    }
    
    fn init_led_functions() -> HashMap<TokenKind, LedFn<'arena, 'src>> {
        let mut table = HashMap::new();
        // Binary operators
        for &(token_kind, _) in OPERATOR_PRECEDENCE {
            if let Some(bp) = Self::get_binding_power(token_kind) {
                if bp != BindingPower::PRIMARY && bp != BindingPower::UNARY {
                    table.insert(token_kind, Self::led_binary_op);
                }
            }
        }
        // Postfix operators
        table.insert(TokenKind::Increment, Self::led_postfix);
        table.insert(TokenKind::Decrement, Self::led_postfix);
        table.insert(TokenKind::LeftParen, Self::led_function_call);
        table.insert(TokenKind::LeftBracket, Self::led_index);
        table.insert(TokenKind::Dot, Self::led_member_access);
        table.insert(TokenKind::Arrow, Self::led_member_access);
        // Conditional operator
        table.insert(TokenKind::Question, Self::led_ternary);
        table
    }
    
    fn init_binding_powers() -> HashMap<TokenKind, BindingPower> {
        let mut table = HashMap::new();
        for &(token_kind, binding_power) in OPERATOR_PRECEDENCE {
            table.insert(token_kind, binding_power);
        }
        table.insert(TokenKind::Increment, BindingPower::POSTFIX);
        table.insert(TokenKind::Decrement, BindingPower::POSTFIX);
        table.insert(TokenKind::LeftParen, BindingPower::POSTFIX);
        table.insert(TokenKind::LeftBracket, BindingPower::POSTFIX);
        table.insert(TokenKind::Dot, BindingPower::POSTFIX);
        table.insert(TokenKind::Arrow, BindingPower::POSTFIX);
        table.insert(TokenKind::Question, BindingPower::TERNARY);
        table
    }
}
```

### Declaration Parsing

```rust
/// Separate declaration parser for C's complex type system
pub struct DeclarationParser<'arena, 'src> {
    parser: &'arena mut Parser<'arena, 'src>,
    allow_abstract_declarators: bool,
    parsing_function_parameters: bool,
}

/// Declaration context for tracking state
pub struct DeclarationContext {
    pub current_storage_class: Option<StorageClass>,
    pub current_type_qualifiers: TypeQualifiers,
    pub current_alignas: Option<&'arena Node<'arena>>,
    pub in_function_parameters: bool,
    pub in_struct_union: bool,
    pub in_enum: bool,
    pub parsing_declaration_specifiers: bool,
}

/// Parse declaration following C11 grammar
pub enum ParseDeclResult<'arena> {
    Declaration(&'arena Node<'arena>),
    FunctionDef(&'arena Node<'arena>),
    Empty, // Just a semicolon
}

/// C declaration specifiers parser
pub struct DeclSpecParser<'arena, 'src> {
    parser: &'arena mut Parser<'arena, 'src>,
    specifiers: Vec<DeclSpecifier<'arena>>,
}
```

### Key Parsing Functions

```rust
impl<'arena, 'src> Parser<'arena, 'src> {
    /// Main expression parsing using Pratt algorithm
    pub fn parse_expression(
        &mut self,
        min_binding_power: BindingPower,
    ) -> Result<ParseExprResult<'arena>, ParseError> {
        let mut left = self.parse_prefix()?;
        
        loop {
            let current_token = &self.tokens[self.current_idx];
            let Some(binding_power) = self.get_binding_power(current_token.kind) else {
                break;
            };
            
            if binding_power < min_binding_power {
                break;
            }
            
            // Handle left-associative operators
            let next_min_bp = if current_token.kind.is_right_associative() {
                BindingPower(binding_power.0 + 1)
            } else {
                binding_power
            };
            
            // Parse the right-hand side
            self.advance()?;
            let right = self.parse_infix(left, current_token, next_min_bp)?;
            left = self.arena.alloc(Node {
                kind: right,
                span: self.compute_span(left.span, current_token.span),
                resolved_type: Cell::new(None),
            });
        }
        
        Ok(ParseExprResult::Expression(left))
    }
    
    /// Parse primary expression
    fn parse_primary(&mut self) -> Result<ParseExprResult<'arena>, ParseError> {
        let token = self.current_token()?;
        
        match token.kind {
            TokenKind::Identifier => {
                let symbol = self.intern_identifier(token.text)?;
                self.advance()?;
                Ok(ParseExprResult::Expression(self.arena.alloc(Node {
                    kind: NodeKind::Ident(symbol),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                })))
            }
            TokenKind::IntegerConstant => {
                let value = self.parse_integer_constant(token.text)?;
                self.advance()?;
                Ok(ParseExprResult::Expression(self.arena.alloc(Node {
                    kind: NodeKind::LiteralInt(value),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                })))
            }
            // ... other literal cases
            _ => {
                Err(ParseError::UnexpectedToken {
                    expected: vec![TokenKind::Identifier, TokenKind::IntegerConstant],
                    found: token,
                    location: token.location,
                })
            }
        }
    }
}
```

### Grammar Strategy

- **Pratt parser for expressions** with full operator precedence
- **Top-down recursive descent** for statements and declarations
- **Separate declaration parser** for C's complex type system
- **Context-aware parsing** for declaration vs expression contexts

### Key Features

- **Full C11 operator precedence** with left/right associativity
- **_Generic selection** parsing with type-based disambiguation
- **Compound literal** support `(type){initializer}`
- **Function pointer** declaration parsing
- **Complex declarator** syntax support (`*(*(*fp)())[10]`)
- **C11 features**: `_Alignas`, `_Atomic`, `_Noreturn`, etc.

## Semantic Analysis Phase

### Responsibilities
- Symbol table management and scope resolution
- Type checking and type equivalence
- Constant expression evaluation
- Declaration checking and validity
- _Static_assert evaluation
- _Generic selection resolution

### Data Structures

```rust
/// Symbol table entry
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind,
    pub type_info: Option<&'arena Type<'arena>>,
    pub storage_class: Option<StorageClass>,
    pub scope: ScopeId,
    pub definition_location: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
}

/// Symbol kinds
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
        initializer: Option<ConstantExpression>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: Vec<ParameterInfo>,
    },
    Typedef {
        underlying_type: &'arena Type<'arena>,
    },
    EnumConstant {
        value: Option<i64>,
    },
    Label {
        is_defined: bool,
        is_used: bool,
    },
    StructOrUnion {
        is_complete: bool,
        members: Option<Vec<MemberInfo>>,
        size: Option<usize>,
        alignment: Option<usize>,
    },
    Macro {
        definition: MacroDef,
        is_builtin: bool,
    },
}

/// Scope management
pub struct ScopeManager {
    scopes: Vec<Scope>,
    current_scope: ScopeId,
    global_scope: ScopeId,
    // For file scope variables
    translation_unit_scope: ScopeId,
}

/// Scope structure
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntry>,
    pub is_block_scope: bool,
    pub function_scope: Option<FunctionScopeId>,
}

/// Type representation (from AST design)
pub struct Type<'arena> {
    pub kind: TypeKind<'arena>,
    pub qualifiers: TypeQualifiers,
    pub size: Option<usize>,
    pub alignment: Option<usize>,
}
```

### Semantic Analysis Algorithm

1. **First pass**: Collect all declarations and build symbol table
2. **Second pass**: Complete type information and resolve forward references
3. **Third pass**: Check semantics and generate warnings/errors
4. **Fourth pass**: Final validation and optimization preparation

### Type System Features

- **Complete type checking** for C11 standard compliance
- **Atomic types** (_Atomic) with proper synchronization semantics
- **Complex types** (_Complex)
- **Alignment specifiers** (_Alignas)
- **Type qualifiers** (const, volatile, restrict, _Atomic)
- **Pointer arithmetic** validation
- **Function type** checking with parameter and return types
- **Array bounds** checking (flexible array members)

## AST Dumper Phase

### Responsibilities
- Visual representation of AST for debugging
- Multiple output formats (DOT, JSON, human-readable text)
- Symbol table visualization
- Type information display
- Performance profiling integration

### Implementation

```rust
/// AST dumper configuration
pub struct DumpConfig {
    pub format: OutputFormat,
    pub include_symbols: bool,
    pub include_types: bool,
    pub include_locations: bool,
    pub max_depth: Option<usize>,
    pub highlight_errors: bool,
}

/// Output formats
pub enum OutputFormat {
    HumanReadable,
    Json,
    Dot, // Graphviz format
    Xml,
}

/// AST dumping interface
pub trait AstDumper {
    fn dump_node(&self, node: &Node, config: &DumpConfig) -> String;
    fn dump_symbol_table(&self, table: &SymbolTable) -> String;
    fn dump_type_info(&self, type_info: &Type) -> String;
}

/// Human-readable formatter
pub struct HumanReadableDumper {
    indent_level: usize,
    line_number: u32,
}

/// JSON formatter
pub struct JsonDumper {
    pretty_print: bool,
}
```

## Data Flow and Integration

### Inter-Phase Communication

```
Preprocessor → [PreprocessedSource] → Lexer
                ↓
Lexer → [TokenStream] → Parser
                ↓
Parser → [AST] → SemanticAnalyzer
                ↓
SemanticAnalyzer → [AnnotatedAST] → ASTDumper
```

### Data Structures Between Phases

```rust
/// Preprocessor output
pub struct PreprocessedSource<'src> {
    pub text: &'src str,
    pub included_files: Vec<SourceFile>,
    pub macro_definitions: HashMap<Symbol, MacroDef>,
    pub line_directives: Vec<LineDirective>,
}

/// Lexer output
pub struct TokenStream<'src> {
    pub tokens: Vec<Token<'src>>,
    pub source_mapping: Vec<SourceMapping>,
    pub total_lines: u32,
}

/// Parser output
pub struct ParseResult<'arena> {
    pub ast: Option<&'arena Node<'arena>>,
    pub parse_errors: Vec<ParseError>,
    pub warnings: Vec<ParseWarning>,
    pub symbol_table: SymbolTable,
}

/// Semantic analysis result
pub struct SemanticResult<'arena> {
    pub annotated_ast: Option<&'arena Node<'arena>>,
    pub semantic_errors: Vec<SemanticError>,
    pub warnings: Vec<SemanticWarning>,
    pub symbol_table: SymbolTable,
    pub type_table: TypeTable,
}
```

## Performance Considerations

### Memory Management

1. **Arena Allocation**: All AST nodes allocated in arena
2. **String Interning**: Reduce memory usage for repeated strings
3. **Zero-Copy Parsing**: Minimize intermediate allocations
4. **Lazy Evaluation**: Only compute when needed

### Cache Optimization

1. **Struct-of-Arrays** layout for repeated data
2. **Hot/Cold Splitting**: Separate frequently accessed from rarely accessed data
3. **Memory Prefetching**: Hint for predictable memory access patterns
4. **Data Locality**: Group related data structures

### Complexity Analysis

| Phase | Time Complexity | Space Complexity |
|-------|----------------|------------------|
| Preprocessing | O(n) | O(m) where m is macro count |
| Lexing | O(n) | O(1) |
| Parsing | O(n) | O(p) where p is precedence levels |
| Semantic Analysis | O(n) | O(s) where s is symbol count |
| AST Dumping | O(n) | O(1) |

## Error Handling Strategy

### Error Types

```rust
/// Comprehensive error types
pub enum CompilerError {
    Preprocessor(PreprocessorError),
    Lexer(LexerError),
    Parser(ParserError),
    Semantic(SemanticError),
    System(SystemError),
}

/// Preprocessor errors
pub enum PreprocessorError {
    MacroRedefinition { name: Symbol, first_def: SourceSpan, second_def: SourceSpan },
    UndefinedMacro { name: Symbol, location: SourceSpan },
    IncludeFileNotFound { path: String, location: SourceSpan },
    RecursiveInclude { file: SourceId, location: SourceSpan },
    InvalidPragma { directive: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Lexer errors
pub enum LexerError {
    InvalidCharacter { ch: char, location: SourceSpan },
    UnterminatedString { location: SourceSpan },
    UnterminatedComment { location: SourceSpan },
    InvalidNumber { text: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Parser errors
pub enum ParserError {
    UnexpectedToken { expected: Vec<TokenKind>, found: Token, location: SourceSpan },
    MissingToken { expected: TokenKind, location: SourceSpan },
    SyntaxError { message: String, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}

/// Semantic errors
pub enum SemanticError {
    UndeclaredIdentifier { name: Symbol, location: SourceSpan },
    Redefinition { name: Symbol, first_def: SourceSpan, second_def: SourceSpan },
    TypeMismatch { expected: String, found: String, location: SourceSpan },
    IncompleteType { name: Symbol, location: SourceSpan },
    // Pratt parser specific errors
    UnclosedParenthesis { location: SourceSpan },
    InvalidExpression { context: String, location: SourceSpan },
    IncompleteDeclaration { expected: String, location: SourceSpan },
    UnterminatedGeneric { location: SourceSpan },
    // ... more variants
}
```

### Error Recovery

1. **Pratt parser error recovery** - stop at minimum binding power
2. **Declaration context recovery** - reset to neutral declaration state
3. **Synchronization points** to resume parsing (semicolons, braces)
4. **Error symbol insertion** to continue processing
5. **Incremental error reporting** to show all errors
6. **Context preservation** for better error messages

### Error Reporting

```rust
/// Error context for better error messages
pub struct ErrorContext {
    pub current_function: Option<Symbol>,
    pub current_file: SourceId,
    pub current_line: u32,
    pub stack_trace: Vec<SourceLocation>,
}

/// Error formatter
pub struct ErrorFormatter {
    pub show_code_snippets: bool,
    pub show_stack_trace: bool,
    pub use_colors: bool,
    pub max_context_lines: usize,
}
```

This design document provides a comprehensive foundation for building a high-performance C11 compiler in Rust. The architecture emphasizes performance, standards compliance, and maintainability while providing robust error handling and debugging capabilities.