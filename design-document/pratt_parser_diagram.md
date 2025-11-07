# Additional Pratt Parser Architecture Diagram

```mermaid
graph TD
    A[Token Stream] --> B[Parser Context]
    B --> C[Expression Parser]
    B --> D[Declaration Parser]
    
    C --> E[Pratt Table]
    E --> F[NUD Functions]
    E --> G[LED Functions]
    E --> H[Binding Powers]
    
    F --> F1[Identifier]
    F --> F2[Literals]
    F --> F3[Unary Ops]
    F --> F4[Sizeof/Alignof]
    F --> F5[Generic]
    F --> F6[Parenthesis]
    
    G --> G1[Binary Ops]
    G --> G2[Postfix Ops]
    G --> G3[Function Call]
    G --> G4[Array Index]
    G --> G5[Member Access]
    G --> G6[Ternary]
    
    D --> D1[DeclSpec Parser]
    D --> D2[Declarator Parser]
    D --> D3[Function Parser]
    
    C --> I[AST Node]
    D --> I
    
    I --> J[Annotated AST]
    J --> K[Semantic Analysis]
    K --> L[Final AST]
```

## Pratt Parser Flow

```mermaid
sequenceDiagram
    participant P as Parser
    participant E as ExpressionParser
    participant T as Pratt Table
    participant N as NUD Functions
    participant L as LED Functions
    
    P->>E: parse_expression(min_bp)
    E->>E: parse_prefix() [NUD]
    E->>T: get_binding_power(token)
    T-->>E: binding_power
    
    alt operator found
        E->>E: check binding_power >= min_bp
        E->>L: parse_infix(left, token, next_bp) [LED]
        L-->>E: right_expression
        E->>E: create_binary_node(left, right)
        E->>E: loop continue
    else no operator
        E-->>P: Expression(left)
    end
```

## C11 Operator Precedence (Pratt Style)

```mermaid
graph LR
    A[Primary] --> B[Postfix]
    B --> C[Unary]
    C --> D[Cast]
    D --> E[Multiplicative]
    E --> F[Additive]
    F --> G[Shift]
    G --> H[Relational]
    H --> I[Equality]
    I --> J[Bitwise AND]
    J --> K[Bitwise XOR]
    K --> L[Bitwise OR]
    L --> M[Logical AND]
    M --> N[Logical OR]
    N --> O[Ternary]
    O --> P[Assignment]
    P --> Q[Comma]