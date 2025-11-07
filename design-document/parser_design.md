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