# Parser Phase Design Document

## Overview

The parser processes the token stream from the lexer and constructs a flattened Abstract Syntax Tree (AST) representing the C11 program's structure. It implements a comprehensive Pratt parser for expressions combined with recursive descent parsing for statements and declarations, with extensive error recovery and support for all C11 language features.

## Responsibilities

- **AST Construction**: Build flattened AST nodes from token stream with index-based references
- **Expression Parsing**: Full Pratt parser implementation with C11 operator precedence
- **Statement/Declaration Parsing**: Recursive descent for all C11 control structures and declarations
- **Complex Declarator Parsing**: Handle C's notoriously complex declaration syntax
- **Error Recovery**: Comprehensive error recovery with synchronization points
- **C11 Feature Support**: Complete implementation of C11 standard including generics, atomics, etc.

## Modular Architecture

The parser is organized into specialized modules for different language constructs:

- **`parser.rs`**: Main parser coordination, public API, and state management
- **`expressions.rs`**: Pratt parser implementation for expressions and operators
- **`statements.rs`**: Statement parsing (compound, if, loops, etc.)
- **`declarations.rs`**: Declaration and function definition parsing
- **`declaration_core.rs`**: Core declaration parsing logic
- **`declarator.rs`**: Complex declarator parsing for C's type system
- **`enum_parsing.rs`**: Enumeration type parsing
- **`struct_parsing.rs`**: Structure and union parsing
- **`type_specifiers.rs`**: Type specifier parsing
- **`type_builder.rs`**: Type construction utilities
- **`utils.rs`**: Parser utilities and helper functions

## Core Data Structures

```rust
/// Main parser structure with borrowing for resource management
pub struct Parser<'tokens, 'ast, 'diag> {
    tokens: &'tokens [Token],
    current_idx: usize,
    ast: &'ast mut Ast,
    diag: &'diag mut DiagnosticEngine,
}

/// Pratt parser binding power for operator precedence
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

/// Expression parsing result
pub enum ParseExprOutput {
    Expression(NodeRef),
    Statement(NodeRef),
}
```

## Expression Parsing Algorithm

The parser implements a full Pratt parser with comprehensive operator precedence handling:

### Binding Power Table

```rust
impl Token {
    pub fn binding_power(&self) -> Option<(BindingPower, Associativity)> {
        match self.kind {
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
```

### Pratt Parser Implementation

```rust
impl<'tokens, 'ast, 'diag> Parser<'tokens, 'ast, 'diag> {
    /// Main expression parsing using Pratt algorithm
    pub fn parse_expression(&mut self, min_bp: BindingPower) -> Result<NodeRef, ParseError> {
        let mut left = self.parse_prefix()?;

        loop {
            let Some((bp, assoc)) = self.current_token()?.binding_power() else {
                break;
            };

            if bp < min_bp {
                break;
            }

            let op_token = self.current_token()?;
            self.advance()?;

            let next_min_bp = match assoc {
                Associativity::Left => bp,
                Associativity::Right => BindingPower(bp.0 + 1),
            };

            let right = self.parse_expression(next_min_bp)?;
            left = self.create_binary_op(op_token, left, right)?;
        }

        Ok(left)
    }

    /// Parse prefix expressions (literals, identifiers, unary operators)
    fn parse_prefix(&mut self) -> Result<NodeRef, ParseError> {
        let token = self.current_token()?;

        match token.kind {
            TokenKind::Identifier => self.parse_identifier(),
            TokenKind::IntegerConstant => self.parse_integer_literal(),
            TokenKind::FloatConstant => self.parse_float_literal(),
            TokenKind::CharacterConstant => self.parse_char_literal(),
            TokenKind::StringLiteral => self.parse_string_literal(),
            TokenKind::LeftParen => self.parse_parenthesized_expression(),
            TokenKind::Plus | TokenKind::Minus | TokenKind::LogicNot |
            TokenKind::BitNot | TokenKind::Star | TokenKind::And |
            TokenKind::Increment | TokenKind::Decrement => self.parse_unary_op(),
            _ => Err(ParseError::UnexpectedToken { /* ... */ }),
        }
    }
}
```

## Declaration and Statement Parsing

### Complex Declarator Parsing

The parser implements comprehensive declarator parsing for C's complex type system:

```rust
impl<'tokens, 'ast, 'diag> Parser<'tokens, 'ast, 'diag> {
    /// Parse a C declarator with full complexity support
    pub fn parse_declarator(&mut self, initial_name: Option<Symbol>) -> Result<Declarator, ParseError> {
        // Parse leading pointers with qualifiers
        let mut pointer_stack = Vec::new();
        while self.current_token()?.kind == TokenKind::Star {
            self.advance()?; // consume '*'
            let qualifiers = self.parse_type_qualifiers()?;
            pointer_stack.push(qualifiers);
        }

        // Parse direct declarator (identifier or parenthesized)
        let mut declarator = if self.current_token()?.kind == TokenKind::LeftParen {
            self.advance()?; // consume '('
            let inner = self.parse_declarator(None)?;
            self.expect(TokenKind::RightParen)?;
            inner
        } else if let Some(name) = initial_name {
            Declarator::Identifier(name, TypeQualifiers::empty(), None)
        } else if self.current_token()?.kind == TokenKind::Identifier {
            let name = self.current_token()?.symbol();
            self.advance()?;
            Declarator::Identifier(name, TypeQualifiers::empty(), None)
        } else {
            return Err(ParseError::ExpectedDeclarator);
        };

        // Parse trailing array and function declarators
        loop {
            match self.current_token()?.kind {
                TokenKind::LeftBracket => {
                    self.advance()?; // consume '['
                    let size = self.parse_array_size()?;
                    self.expect(TokenKind::RightBracket)?;
                    declarator = Declarator::Array(Box::new(declarator), size);
                }
                TokenKind::LeftParen => {
                    self.advance()?; // consume '('
                    let params = self.parse_parameter_list()?;
                    self.expect(TokenKind::RightParen)?;
                    declarator = Declarator::Function(Box::new(declarator), params);
                }
                _ => break,
            }
        }

        // Apply pointer stack in reverse order
        for qualifiers in pointer_stack.into_iter().rev() {
            declarator = Declarator::Pointer(qualifiers, Some(Box::new(declarator)));
        }

        Ok(declarator)
    }
}
```

### Statement Parsing

The parser handles all C11 statement types with proper control flow:

```rust
impl<'tokens, 'ast, 'diag> Parser<'tokens, 'ast, 'diag> {
    /// Parse any statement
    pub fn parse_statement(&mut self) -> Result<NodeRef, ParseError> {
        match self.current_token()?.kind {
            TokenKind::LeftBrace => self.parse_compound_statement(),
            TokenKind::If => self.parse_if_statement(),
            TokenKind::Switch => self.parse_switch_statement(),
            TokenKind::While => self.parse_while_statement(),
            TokenKind::Do => self.parse_do_while_statement(),
            TokenKind::For => self.parse_for_statement(),
            TokenKind::Goto => self.parse_goto_statement(),
            TokenKind::Continue => self.parse_continue_statement(),
            TokenKind::Break => self.parse_break_statement(),
            TokenKind::Return => self.parse_return_statement(),
            TokenKind::Semicolon => self.parse_empty_statement(),
            TokenKind::Identifier if self.peek_token()?.kind == TokenKind::Colon => {
                self.parse_labeled_statement()
            }
            _ => self.parse_expression_statement(),
        }
    }

    /// Parse compound statement with declarations and statements
    fn parse_compound_statement(&mut self) -> Result<NodeRef, ParseError> {
        self.expect(TokenKind::LeftBrace)?;
        let mut items = Vec::new();

        while self.current_token()?.kind != TokenKind::RightBrace &&
              self.current_token()?.kind != TokenKind::EndOfFile {
            if self.is_declaration_start() {
                items.push(self.parse_declaration()?);
            } else {
                items.push(self.parse_statement()?);
            }
        }

        self.expect(TokenKind::RightBrace)?;
        Ok(self.ast.push_node(Node {
            kind: NodeKind::CompoundStatement(items),
            span: /* calculated span */,
            resolved_type: Cell::new(None),
            resolved_symbol: Cell::new(None),
        }))
    }
}
```

## Error Recovery Strategy

The parser implements comprehensive error recovery:

```rust
impl<'tokens, 'ast, 'diag> Parser<'tokens, 'ast, 'diag> {
    /// Advance to next synchronization point after error
    fn synchronize(&mut self) {
        while self.current_idx < self.tokens.len() {
            match self.current_token().unwrap().kind {
                // Synchronization points
                TokenKind::Semicolon => {
                    self.advance().unwrap();
                    break;
                }
                TokenKind::RightBrace => break,
                TokenKind::If | TokenKind::For | TokenKind::While |
                TokenKind::Return | TokenKind::Break | TokenKind::Continue => break,
                _ => { self.advance().unwrap(); }
            }
        }
    }

    /// Parse with error recovery
    fn parse_with_recovery<F, T>(&mut self, parse_fn: F) -> Result<T, ParseError>
    where F: FnOnce(&mut Self) -> Result<T, ParseError> {
        match parse_fn(self) {
            Ok(result) => Ok(result),
            Err(e) => {
                // Report error
                self.diag.report_error(/* ... */);

                // Attempt recovery
                self.synchronize();

                // Return error node or recovered result
                Err(e)
            }
        }
    }
}
```

## Key Features

### Complete C11 Support

- **All operators** with correct precedence and associativity
- **Complex declarations** including function pointers, arrays, and nested pointers
- **Control structures** including if/else, loops, switch statements
- **C11 features**: `_Generic`, `_Static_assert`, `_Atomic`, `_Alignas`, etc.
- **Anonymous structures/unions** in declarators

### Performance Optimizations

- **Index-based AST construction** for cache efficiency
- **Borrowed token stream** to avoid copying
- **Interior mutability** for semantic annotations
- **Streaming parsing** without intermediate representations

### Error Handling

- **Precise error locations** with source spans
- **Multiple error reporting** continues after first error
- **Recovery synchronization** at statement/declaration boundaries
- **Context-aware messages** for better diagnostics

## Integration with Compiler Pipeline

The parser integrates seamlessly with the compiler pipeline:

- **Input**: `&[Token]` from lexer with borrowed references
- **Output**: Flattened AST with `NodeRef` indices
- **Error reporting**: Direct integration with `DiagnosticEngine`
- **Memory management**: Scoped borrowing prevents resource conflicts
- **Source locations**: Preserved through `SourceSpan` in all nodes

This comprehensive parser implementation provides a solid foundation for the C11 compiler, handling the full complexity of the C language with robust error recovery and high performance.