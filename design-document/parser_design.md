## Parser Phase

### Overview

The parser processes the token stream from the lexer and constructs an Abstract Syntax Tree (AST) representing the C11 program's structure. It uses a hybrid parsing approach combining Pratt parsing for expressions with recursive descent for statements and declarations.

### Responsibilities

- **AST Construction**: Build flattened AST nodes from token stream
- **Expression Parsing**: Use Pratt parser for operator precedence handling
- **Statement/Declaration Parsing**: Recursive descent for control structures and declarations
- **Error Recovery**: Continue parsing after syntax errors for better diagnostics
- **C11 Feature Support**: Handle all C11 syntax including generics, atomics, etc.

### Core Data Structures

```rust
/// Main parser structure
pub struct Parser<'arena, 'src> {
    tokens: &'src [Token],
    current_idx: usize,
    ast: &'arena mut Ast,
    diag: &'src DiagnosticEngine,

    // Parsing context
    in_function_body: bool,
    in_struct_declaration: bool,
    in_enum_declaration: bool,

    // Error recovery state
    error_recovery_points: Vec<ErrorRecoveryPoint>,
}

/// Binding power for Pratt parser operator precedence
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindingPower(u8);

impl BindingPower {
    pub const MIN: Self = Self(0);
    pub const ASSIGNMENT: Self = Self(10);
    pub const CONDITIONAL: Self = Self(20);
    pub const LOGICAL_OR: Self = Self(30);
    pub const LOGICAL_AND: Self = Self(40);
    pub const BITWISE_OR: Self = Self(50);
    pub const BITWISE_XOR: Self = Self(60);
    pub const BITWISE_AND: Self = Self(70);
    pub const EQUALITY: Self = Self(80);
    pub const RELATIONAL: Self = Self(90);
    pub const SHIFT: Self = Self(100);
    pub const ADDITIVE: Self = Self(110);
    pub const MULTIPLICATIVE: Self = Self(120);
    pub const CAST: Self = Self(130);
    pub const UNARY: Self = Self(140);
    pub const POSTFIX: Self = Self(150);
    pub const PRIMARY: Self = Self(160);
}

/// Pratt parser implementation
pub struct PrattParser;

impl PrattParser {
    pub fn get_binding_power(token_kind: TokenKind) -> Option<(BindingPower, Associativity)> {
        match token_kind {
            // Assignment operators (right-associative)
            TokenKind::Assign | TokenKind::PlusAssign | TokenKind::MinusAssign |
            TokenKind::StarAssign | TokenKind::DivAssign | TokenKind::ModAssign |
            TokenKind::AndAssign | TokenKind::OrAssign | TokenKind::XorAssign |
            TokenKind::LeftShiftAssign | TokenKind::RightShiftAssign =>
                Some((BindingPower::ASSIGNMENT, Associativity::Right)),

            // Conditional operator (right-associative)
            TokenKind::Question => Some((BindingPower::CONDITIONAL, Associativity::Right)),

            // Logical operators (left-associative)
            TokenKind::LogicOr => Some((BindingPower::LOGICAL_OR, Associativity::Left)),
            TokenKind::LogicAnd => Some((BindingPower::LOGICAL_AND, Associativity::Left)),

            // Bitwise operators (left-associative)
            TokenKind::Or => Some((BindingPower::BITWISE_OR, Associativity::Left)),
            TokenKind::Xor => Some((BindingPower::BITWISE_XOR, Associativity::Left)),
            TokenKind::And => Some((BindingPower::BITWISE_AND, Associativity::Left)),

            // Comparison operators (left-associative)
            TokenKind::Equal | TokenKind::NotEqual =>
                Some((BindingPower::EQUALITY, Associativity::Left)),
            TokenKind::Less | TokenKind::Greater | TokenKind::LessEqual | TokenKind::GreaterEqual =>
                Some((BindingPower::RELATIONAL, Associativity::Left)),

            // Shift operators (left-associative)
            TokenKind::LeftShift | TokenKind::RightShift =>
                Some((BindingPower::SHIFT, Associativity::Left)),

            // Additive operators (left-associative)
            TokenKind::Plus | TokenKind::Minus =>
                Some((BindingPower::ADDITIVE, Associativity::Left)),

            // Multiplicative operators (left-associative)
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent =>
                Some((BindingPower::MULTIPLICATIVE, Associativity::Left)),

            // Postfix operators
            TokenKind::Increment | TokenKind::Decrement | TokenKind::LeftParen |
            TokenKind::LeftBracket | TokenKind::Dot | TokenKind::Arrow =>
                Some((BindingPower::POSTFIX, Associativity::Left)),

            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
}
```

### Expression Parsing Algorithm

The parser uses a Pratt parser for expressions, which handles operator precedence and associativity naturally:

1. **Parse Prefix Expression**: Start with primary expressions (literals, identifiers, parentheses)
2. **Infix Operator Loop**: While current token has higher precedence than minimum:
   - Consume operator token
   - Recursively parse right-hand side with appropriate precedence
   - Create binary/unary operation node
3. **Associativity Handling**: Adjust minimum precedence based on operator associativity

**Example: Parsing `a + b * c`**

```
Input: [Identifier(a), Plus, Identifier(b), Star, Identifier(c)]

1. Parse prefix: Identifier(a) → left = Ident(a)
2. Current token: Plus (precedence 110)
   Min precedence: 0 → continue
3. Consume Plus, parse right with precedence 111
4. Parse prefix: Identifier(b) → right = Ident(b)
5. Current token: Star (precedence 120 > 111) → continue
6. Consume Star, parse right with precedence 121
7. Parse prefix: Identifier(c) → right = Ident(c)
8. No more tokens → return BinaryOp(Mul, Ident(b), Ident(c))
9. Return BinaryOp(Add, Ident(a), BinaryOp(Mul, Ident(b), Ident(c)))
```

**Key Implementation Details:**
- **Binding Power Table**: Maps each operator to precedence level and associativity
- **Prefix Parsers**: Handle literals, identifiers, unary operators, parentheses
- **Infix Parsers**: Handle binary operators, ternary, function calls, array access
- **Postfix Parsers**: Handle increment/decrement, member access

### Declaration and Statement Parsing

The parser uses recursive descent for declarations and statements, with special handling for C's complex type system:

**Declaration Parsing:**
1. **Declaration Specifiers**: Parse storage class, type qualifiers, type specifiers
2. **Declarators**: Handle complex pointer, array, function syntax
3. **Initializers**: Parse expressions or compound initializers
4. **Context Awareness**: Distinguish between declarations and expressions

**Key Challenges:**
- **Type vs Expression Ambiguity**: `int *x;` vs `int *y;`
- **Complex Declarators**: `int (*(*fp)())[10];`
- **Abstract Declarators**: For casts and sizeof

**Statement Parsing:**
- **Compound Statements**: Block scope with declarations and statements
- **Selection**: if/else, switch statements
- **Iteration**: while, do-while, for loops
- **Jump**: goto, continue, break, return

### Integration with Compiler Pipeline

The parser receives a `Token` stream from the lexer and produces a flattened AST that feeds into semantic analysis. Key integration points:

- **Token Stream Input**: Consumes `&[Token]` from lexer output
- **AST Construction**: Builds nodes in the shared `Ast` structure
- **Source Location Preservation**: Maintains accurate span information for error reporting
- **Incremental Parsing**: Can parse individual declarations or entire translation units

### Error Recovery Strategy

The parser implements robust error recovery to continue parsing after syntax errors:

1. **Synchronization Points**: Skip to statement boundaries (semicolons, braces, keywords)
2. **Error Nodes**: Insert placeholder nodes in AST for malformed constructs
3. **Context Preservation**: Maintain parsing state across error recovery
4. **Multiple Error Reporting**: Continue parsing to find additional issues

**Example Error Recovery:**
```c
int x = ;    // Missing initializer
int y = 10;  // Parser recovers and continues
```

The parser would report the missing initializer error but successfully parse the second declaration.

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
    ) -> Result<ParseExprOutput, ParseError> {
        let mut left = self.parse_prefix()?;

        loop {
            let current_token = &self.tokens[self.current_idx];
            let Some(binding_power) = PrattParser::get_binding_power(current_token.kind) else {
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
            let left_span = self.ast.get_node(left).span;
            let right_span = self.ast.get_node(right).span;
            let span = SourceSpan { start: left_span.start, end: right_span.end };
            left = self.ast.push_node(Node {
                kind: right,
                span,
                resolved_type: Cell::new(None),
                resolved_symbol: Cell::new(None),
            });
        }

        Ok(ParseExprOutput::Expression(left))
    }

    /// Parse primary expression
    fn parse_primary(&mut self) -> Result<ParseExprOutput, ParseError> {
        let token = self.current_token()?;

        match token.kind {
            TokenKind::Identifier => {
                let symbol = self.intern_identifier(token.text)?;
                self.advance()?;
                let node = self.ast.push_node(Node {
                    kind: NodeKind::Ident(symbol, Cell::new(None)),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(ParseExprOutput::Expression(node))
            }
            TokenKind::IntegerConstant => {
                let value = self.parse_integer_constant(token.text)?;
                self.advance()?;
                let node = self.ast.push_node(Node {
                    kind: NodeKind::LiteralInt(value),
                    span: token.location.into(),
                    resolved_type: Cell::new(None),
                    resolved_symbol: Cell::new(None),
                });
                Ok(ParseExprOutput::Expression(node))
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
    pub fn parse_declarator(&mut self, initial_declarator: Option<Symbol>) -> Result<Declarator, ParseError> {
        let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
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
            Declarator::Identifier(ident_symbol, TypeQualifiers(0), None)
        } else if self.current_token_kind()? == TokenKind::Identifier {
            let ident_token = self.current_token()?;
            let ident_symbol = self.intern_identifier(ident_token.text)?;
            self.advance()?; // Consume identifier
            Declarator::Identifier(ident_symbol, TypeQualifiers(0), None)
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
                    current_base = Declarator::Array(Box::new(current_base), array_size);
                }
                TokenKind::LeftParen => { // Function declarator
                    self.advance()?; // Consume '('
                    let parameters = self.parse_function_parameters()?;
                    self.expect(TokenKind::RightParen)?; // Consume ')'
                    current_base = Declarator::Function(Box::new(current_base), parameters);
                }
                _ => break,
            }
        }

        // Reconstruct the declarator chain in reverse order
        let mut final_declarator = current_base;
        for component in declarator_chain.into_iter().rev() {
            final_declarator = match component {
                DeclaratorComponent::Pointer(qualifiers) => Declarator::Pointer(qualifiers, Some(Box::new(final_declarator))),
                // Other components would be handled here if they could precede the identifier
            };
        }

        Ok(final_declarator)
    }

    /// Helper to parse type qualifiers (const, volatile, restrict, _Atomic)
    fn parse_type_qualifiers(&mut self) -> Result<TypeQualifiers, ParseError> {
        let mut qualifiers = TypeQualifiers::empty();
        loop {
            match self.current_token_kind()? {
                TokenKind::Const => {
                    qualifiers.insert(TypeQualifiers::CONST);
                    self.advance()?;
                }
                TokenKind::Volatile => {
                    qualifiers.insert(TypeQualifiers::VOLATILE);
                    self.advance()?;
                }
                TokenKind::Restrict => {
                    qualifiers.insert(TypeQualifiers::RESTRICT);
                    self.advance()?;
                }
                TokenKind::Atomic => { // C11 _Atomic
                    qualifiers.insert(TypeQualifiers::ATOMIC);
                    self.advance()?;
                }
                _ => break,
            }
        }
        Ok(qualifiers)
    }

    /// Helper to parse array size (e.g., `10`, `*`, or empty `[]`)
    fn parse_array_size(&mut self) -> Result<ArraySize, ParseError> {
        match self.current_token_kind()? {
            TokenKind::Star => {
                self.advance()?;
                Ok(ArraySize::Star)
            }
            TokenKind::RightBracket => { // Empty []
                Ok(ArraySize::Incomplete)
            }
            _ => {
                // Assume it's an expression for the size
                let expr_result = self.parse_expression(BindingPower::MIN)?;
                match expr_result {
                    ParseExprOutput::Expression(expr_node) => Ok(ArraySize::Expression(expr_node)),
                    _ => Err(ParseError::SyntaxError { message: "Expected array size expression".to_string(), location: self.current_token()?.location }),
                }
            }
        }
    }

    /// Helper to parse function parameters
    fn parse_function_parameters(&mut self) -> Result<Vec<ParamData>, ParseError> {
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
        Ok(params)
    }
}

/// Helper enum for reconstructing complex declarators
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
    // Function(Vec<ParamData>), // If function could be part of chain
    // Array(ArraySize), // If array could be part of chain
}
```

### Complex C Declaration Parsing (Cdecl)

Parsing complex C declarations like `int (*(*fp)())[10];` is notoriously difficult due to their "spiral" nature. The `DeclarationParser` and `Declarator` enum are designed to handle this.

The `Declarator` enum is recursive, allowing it to represent nested pointer, array, and function types.

-   `Identifier(Symbol, TypeQualifiers, Option<Box<Declarator>>)`: The base case, representing the name being declared, potentially with qualifiers and an inner declarator (for `typedef` or abstract declarators).
-   `Pointer(TypeQualifiers, Option<Box<Declarator>>)`: Represents a pointer, with its own type qualifiers (e.g., `const *`). The `Option<Box<Declarator>>` points to the type it points to.
-   `Array(Box<Declarator>, ArraySize)`: Represents an array, where the first `Declarator` is the element type, and `ArraySize` defines its dimensions.
-   `Function(Box<Declarator>, Vec<ParamData> /* parameters */)`: Represents a function, where the first `Declarator` is the return type, and `ParamData` describes its parameters.

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