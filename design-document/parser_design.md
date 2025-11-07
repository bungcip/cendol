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
    // Parser errors and warnings are defined in error_handling_design.md
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
pub enum ParseExprOutput<'arena> {
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
use hashbrown::HashMap;

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
    ) -> Result<ParseExprOutput<'arena>, ParseError> {
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
        
        Ok(ParseExprOutput::Expression(left))
    }
    
    /// Parse primary expression
    fn parse_primary(&mut self) -> Result<ParseExprOutput<'arena>, ParseError> {
        let token = self.current_token()?;
        
        match token.kind {
            TokenKind::Identifier => {
                let symbol = self.intern_identifier(token.text)?;
                self.advance()?;
                Ok(ParseExprOutput::Expression(self.arena.alloc(Node {
                    kind: NodeKind::Ident(symbol),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                })))
            }
            TokenKind::IntegerConstant => {
                let value = self.parse_integer_constant(token.text)?;
                self.advance()?;
                Ok(ParseExprOutput::Expression(self.arena.alloc(Node {
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
- **Context-aware parsing** for declaration vs expression contexts, especially for disambiguating `*` and `(`
- **Disambiguation of `a * b;`**: The C grammar is highly ambiguous. Constructs like `a * b;` can be either a multiplication expression or a declaration of a pointer `b` of type `a`. This is resolved by maintaining a set of known `typedef` names and type specifiers. When a `*` or `(` is encountered after an identifier, the parser performs a "tentative parse" or "lookahead" to determine if the sequence can form a valid declaration. If it can, and the preceding identifier is a known type name, it's parsed as a declaration; otherwise, it's an expression.

### Key Parsing Functions

```rust
impl<'arena, 'src> Parser<'arena, 'src> {
    /// Main expression parsing using Pratt algorithm
    pub fn parse_expression(
        &mut self,
        min_binding_power: BindingPower,
    ) -> Result<ParseExprOutput<'arena>, ParseError> {
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
        
        Ok(ParseExprOutput::Expression(left))
    }
    
    /// Parse primary expression
    fn parse_primary(&mut self) -> Result<ParseExprOutput<'arena>, ParseError> {
        let token = self.current_token()?;
        
        match token.kind {
            TokenKind::Identifier => {
                let symbol = self.intern_identifier(token.text)?;
                self.advance()?;
                Ok(ParseExprOutput::Expression(self.arena.alloc(Node {
                    kind: NodeKind::Ident(symbol),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                })))
            }
            TokenKind::IntegerConstant => {
                let value = self.parse_integer_constant(token.text)?;
                self.advance()?;
                Ok(ParseExprOutput::Expression(self.arena.alloc(Node {
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

    /// Disambiguates between a type name and an identifier in ambiguous contexts.
    /// This is crucial for parsing C's "declaration-specifier-list" vs "expression" ambiguity.
    fn is_type_name(&self, symbol: Symbol) -> bool {
        // This function would query the symbol table (from semantic analysis)
        // to check if 'symbol' is currently known as a typedef name or a type specifier.
        // For parsing, a simpler heuristic might be used, or a full tentative parse.
        // For now, assume a placeholder.
        false // Placeholder
    }

    /// Parses a C declarator, handling complex pointer, array, and function syntax.
    /// This function is recursive and builds the Declarator enum structure.
    pub fn parse_declarator(&mut self, initial_declarator: Option<Symbol>) -> Result<&'arena Declarator<'arena>, ParseError> {
        let mut declarator_chain: Vec<DeclaratorComponent<'arena>> = Vec::new();
        let mut current_qualifiers = TypeQualifiers(0);

        // Parse leading pointers and their qualifiers
        while self.current_token_kind()? == TokenKind::Star {
            self.advance()?; // Consume '*'
            current_qualifiers = self.parse_type_qualifiers()?;
            declarator_chain.push(DeclaratorComponent::Pointer(current_qualifiers));
            current_qualifiers = TypeQualifiers(0); // Reset for next component
        }

        // Parse direct declarator (identifier or parenthesized declarator)
        let base_declarator = if self.current_token_kind()? == TokenKind::LeftParen {
            self.advance()?; // Consume '('
            let inner_declarator = self.parse_declarator(None)?; // Recursive call for inner declarator
            self.expect(TokenKind::RightParen)?; // Consume ')'
            inner_declarator
        } else if let Some(ident_symbol) = initial_declarator {
            self.arena.alloc(Declarator::Identifier(ident_symbol, TypeQualifiers(0), None))
        } else if self.current_token_kind()? == TokenKind::Identifier {
            let ident_token = self.current_token()?;
            let ident_symbol = self.intern_identifier(ident_token.text)?;
            self.advance()?; // Consume identifier
            self.arena.alloc(Declarator::Identifier(ident_symbol, TypeQualifiers(0), None))
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: vec![TokenKind::Star, TokenKind::LeftParen, TokenKind::Identifier],
                found: self.current_token()?,
                location: self.current_token()?.location,
            });
        };

        // Parse trailing array and function declarators
        let mut current_base = base_declarator;
        loop {
            match self.current_token_kind()? {
                TokenKind::LeftBracket => { // Array declarator
                    self.advance()?; // Consume '['
                    let array_size = self.parse_array_size()?;
                    self.expect(TokenKind::RightBracket)?; // Consume ']'
                    current_base = self.arena.alloc(Declarator::Array(current_base, array_size));
                }
                TokenKind::LeftParen => { // Function declarator
                    self.advance()?; // Consume '('
                    let parameters = self.parse_function_parameters()?;
                    self.expect(TokenKind::RightParen)?; // Consume ')'
                    current_base = self.arena.alloc(Declarator::Function(current_base, parameters));
                }
                _ => break,
            }
        }

        // Reconstruct the declarator chain in reverse order
        let mut final_declarator = current_base;
        for component in declarator_chain.into_iter().rev() {
            final_declarator = match component {
                DeclaratorComponent::Pointer(qualifiers) => self.arena.alloc(Declarator::Pointer(qualifiers, Some(final_declarator))),
                // Other components would be handled here if they could precede the identifier
            };
        }

        Ok(final_declarator)
    }

    /// Helper to parse type qualifiers (const, volatile, restrict, _Atomic)
    fn parse_type_qualifiers(&mut self) -> Result<TypeQualifiers, ParseError> {
        let mut qualifiers = TypeQualifiers(0);
        loop {
            match self.current_token_kind()? {
                TokenKind::Const => {
                    qualifiers.0 |= TypeQualifiers::CONST.0;
                    self.advance()?;
                }
                TokenKind::Volatile => {
                    qualifiers.0 |= TypeQualifiers::VOLATILE.0;
                    self.advance()?;
                }
                TokenKind::Restrict => {
                    qualifiers.0 |= TypeQualifiers::RESTRICT.0;
                    self.advance()?;
                }
                TokenKind::Atomic => { // C11 _Atomic
                    qualifiers.0 |= TypeQualifiers::ATOMIC.0;
                    self.advance()?;
                }
                _ => break,
            }
        }
        Ok(qualifiers)
    }

    /// Helper to parse array size (e.g., `10`, `*`, or empty `[]`)
    fn parse_array_size(&mut self) -> Result<&'arena ArraySize<'arena>, ParseError> {
        match self.current_token_kind()? {
            TokenKind::Star => {
                self.advance()?;
                Ok(self.arena.alloc(ArraySize::Star))
            }
            TokenKind::RightBracket => { // Empty []
                Ok(self.arena.alloc(ArraySize::Incomplete))
            }
            _ => {
                // Assume it's an expression for the size
                let expr_result = self.parse_expression(BindingPower::MIN)?;
                match expr_result {
                    ParseExprOutput::Expression(expr_node) => Ok(self.arena.alloc(ArraySize::Expression(expr_node))),
                    _ => Err(ParseError::SyntaxError { message: "Expected array size expression".to_string(), location: self.current_token()?.location }),
                }
            }
        }
    }

    /// Helper to parse function parameters
    fn parse_function_parameters(&mut self) -> Result<&'arena [ParamData<'arena>], ParseError> {
        let mut params = Vec::new();
        // Placeholder for parsing parameter list
        // This would involve parsing declaration specifiers and declarators for each parameter
        while self.current_token_kind()? != TokenKind::RightParen && self.current_token_kind()? != TokenKind::Ellipsis {
            // Parse DeclSpecifier and Declarator for each parameter
            // For simplicity, just consume tokens for now
            self.advance()?;
        }
        if self.current_token_kind()? == TokenKind::Ellipsis {
            self.advance()?; // Consume '...' for variadic functions
        }
        Ok(self.arena.alloc_slice_copy(&params))
    }
}

/// Helper enum for reconstructing complex declarators
enum DeclaratorComponent<'arena> {
    Pointer(TypeQualifiers),
    // Function(Vec<ParamData<'arena>>), // If function could be part of chain
    // Array(ArraySize<'arena>), // If array could be part of chain
}

```

### Complex C Declaration Parsing (Cdecl)

Parsing complex C declarations like `int (*(*fp)())[10];` is notoriously difficult due to their "spiral" nature. The `DeclarationParser` and `Declarator` enum are designed to handle this.

The `Declarator` enum is recursive, allowing it to represent nested pointer, array, and function types.

-   `Identifier(Symbol, TypeQualifiers, Option<&'arena Declarator<'arena>>)`: The base case, representing the name being declared, potentially with qualifiers and an inner declarator (for `typedef` or abstract declarators).
-   `Pointer(TypeQualifiers, Option<&'arena Declarator<'arena>>)`: Represents a pointer, with its own type qualifiers (e.g., `const *`). The `Option<&'arena Declarator<'arena>>` points to the type it points to.
-   `Array(&'arena Declarator<'arena>, &'arena ArraySize<'arena>)`: Represents an array, where the first `Declarator` is the element type, and `ArraySize` defines its dimensions.
-   `Function(&'arena Declarator<'arena>, &'arena [ParamData<'arena>] /* parameters */)`: Represents a function, where the first `Declarator` is the return type, and `ParamData` describes its parameters.

**Example Walkthrough: `int (*(*fp)())[10];`**

1.  **`int`**: This is parsed by `DeclSpecParser` as a `TypeSpecifier::Int`.
2.  **`(*(*fp)())[10]`**: This is the complex declarator parsed by `parse_declarator`.
    -   The outermost `[10]` is an `Array` declarator. Its element type is `(*(*fp)())`.
    -   The `(*(*fp)())` is a `Pointer` declarator. Its pointee type is `(*fp)()`.
    -   The `(*fp)()` is a `Function` declarator. Its return type is `*fp`.
    -   The `*fp` is a `Pointer` declarator. Its pointee type is `fp`.
    -   The `fp` is an `Identifier` declarator.

The `parse_declarator` function works by first parsing any leading pointers, then the "direct declarator" (which can be an identifier or a parenthesized complex declarator), and finally any trailing array or function declarators. The `DeclaratorComponent` enum helps in reconstructing the nested structure correctly.

### Key Features

- **Full C11 operator precedence** with left/right associativity
- **_Generic selection** parsing with type-based disambiguation
- **Compound literal** support `(type){initializer}`
- **Function pointer** declaration parsing
- **Complex declarator** syntax support (`*(*(*fp)())[10]`)
- **C11 features**: `_Alignas` (as a declaration specifier), `_Atomic` (as a type specifier and qualifier), `_Noreturn` (as a function specifier), etc.

### Error Handling and Recovery Examples

The parser employs a robust error handling strategy to provide meaningful diagnostics and attempt recovery to continue parsing as much of the input as possible.

#### Error Handling Algorithm

1.  **Immediate Error Reporting**: When a syntax error is detected (e.g., unexpected token, missing token), a `ParseError` is immediately generated with precise `SourceSpan` information.
2.  **Error Recovery Points**: The parser defines "synchronization points" (e.g., semicolons, closing braces, keywords like `if`, `for`, `return`). When an error occurs, the parser attempts to skip tokens until it reaches one of these synchronization points.
3.  **Context Preservation**: The `error_recovery_stack` helps in maintaining parsing context during recovery, allowing the parser to pop back to a stable state.
4.  **Tentative Parsing for Ambiguity**: As discussed with `a * b;`, tentative parsing is used to resolve ambiguities without committing to a parse path until enough context is available. If a tentative parse fails, the parser backtracks and tries an alternative.
5.  **Insertion/Deletion**: In some cases, the parser might implicitly "insert" a missing token (e.g., a semicolon) or "delete" an unexpected token to continue parsing, reporting a warning or error.
6.  **Error Nodes in AST**: For severe errors, an `Error` variant in `NodeKind` or `TypeKind` can be inserted into the AST to represent the malformed construct, allowing subsequent phases (like semantic analysis) to still traverse the tree without crashing.

#### Example Cases

Here are some examples of incorrect C11 input and how the parser would handle them:

**Case 1: Missing Semicolon**

```c
int x = 10
int y = 20;
```

-   **Input**: `int x = 10` followed by `int y = 20;`
-   **Expected Error**: `ParseError::MissingToken { expected: TokenKind::Semicolon, location: SourceSpan { start: ..., end: ... } }` pointing to the end of line 1.
-   **Recovery**: The parser would detect the missing semicolon, report the error, and then likely treat `int y = 20;` as a new, separate declaration, effectively recovering by assuming the semicolon was present.

**Case 2: Unmatched Parenthesis in Expression**

```c
int result = (10 + 5;
```

-   **Input**: `int result = (10 + 5;`
-   **Expected Error**: `ParseError::UnclosedParenthesis { location: SourceSpan { start: ..., end: ... } }` pointing to the opening parenthesis.
-   **Recovery**: The Pratt parser, when expecting a `RightParen` but finding a `Semicolon`, would report the error. It might then skip to the semicolon, effectively treating the expression as incomplete but allowing the parsing of subsequent statements.

**Case 3: Invalid Type Specifier in Declaration**

```c
invalid_type my_var;
```

-   **Input**: `invalid_type my_var;`
-   **Expected Error**: `ParseError::UnexpectedToken { expected: vec![...valid type specifiers...], found: TokenKind::Identifier("invalid_type"), location: SourceSpan { start: ..., end: ... } }`
-   **Recovery**: If `invalid_type` is not a known `typedef` or built-in type, the `DeclSpecParser` would fail. The parser might then attempt to skip to the next semicolon or a known statement keyword to continue.

**Case 4: Malformed Function Call**

```c
my_function(arg1 arg2);
```

-   **Input**: `my_function(arg1 arg2);` (missing comma)
-   **Expected Error**: `ParseError::MissingToken { expected: TokenKind::Comma, location: SourceSpan { start: ..., end: ... } }` pointing to `arg2`.
-   **Recovery**: The parser would report the missing comma. It might then attempt to parse `arg2` as a new argument, or skip `arg2` and continue parsing from the closing parenthesis, depending on the specific recovery strategy.

**Case 5: Incomplete Declaration**

```c
int *ptr = ;
```

-   **Input**: `int *ptr = ;`
-   **Expected Error**: `ParseError::InvalidExpression { context: "initializer", location: SourceSpan { start: ..., end: ... } }` pointing to the semicolon after `=`.
-   **Recovery**: The parser expects an expression after `=`, but finds a semicolon. It would report the error and then proceed as if the initializer was empty or malformed, continuing to the next statement.

These examples illustrate how the parser aims to provide precise error messages and recover gracefully, allowing the compilation process to continue and report multiple issues rather than halting on the first error.