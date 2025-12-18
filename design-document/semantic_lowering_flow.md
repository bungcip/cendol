# Semantic Lowering Process Flow

## Overview Diagram

```mermaid
flowchart TD
    A[Parser AST] --> B[Symbol Collection]
    B --> C[Semantic Lowering]
    C --> D[Name Resolution]
    D --> E[Type Resolution]
    E --> F[Type Checking]
    F --> G[Semantic AST/HIR]

    style A fill:#f9f,stroke:#333
    style B fill:#bbf,stroke:#333
    style C fill:#f96,stroke:#333,stroke-width:2px
    style D fill:#bbf,stroke:#333
    style E fill:#bbf,stroke:#333
    style F fill:#bbf,stroke:#333
    style G fill:#9f9,stroke:#333
```

## Detailed Lowering Process

```mermaid
flowchart TD
    subgraph DeclarationLowering[Declaration Lowering Process]
        A1[NodeKind::Declaration] --> B1[lower_declaration]
        B1 --> C1[lower_decl_specifiers]
        B1 --> D1[lower_init_declarator]
        
        C1 --> E1[Process Storage Classes]
        C1 --> F1[Process Type Qualifiers]
        C1 --> G1[Process Type Specifiers]
        C1 --> H1[Validate Combinations]
        
        D1 --> I1[Resolve Final Type]
        D1 --> J1[Handle Typedefs]
        D1 --> K1[Distinguish Functions/Variables]
        D1 --> L1[Create Semantic Nodes]
        D1 --> M1[Update Symbol Table]
        
        E1 --> N1[Check Duplicate Storage]
        G1 --> O1[Merge Type Specifiers]
        H1 --> P1[Validate Typedef+Storage]
        
        I1 --> Q1[Apply Declarator Transformations]
        J1 --> R1[Create TypedefDecl]
        K1 --> S1[Create FunctionDecl]
        K1 --> T1[Create VarDecl]
    end
    
    style DeclarationLowering fill:#f96,stroke:#333,stroke-width:2px
    style A1 fill:#ff9,stroke:#333
    style B1 fill:#9f9,stroke:#333
    style C1 fill:#9f9,stroke:#333
    style D1 fill:#9f9,stroke:#333
```

## Type Resolution Flow

```mermaid
flowchart TD
    subgraph TypeResolution[Type Resolution Process]
        A2[Type Specifiers] --> B2[resolve_type_specifier]
        B2 --> C2[Handle Basic Types]
        B2 --> D2[Handle Typedef Names]
        B2 --> E2[Handle Complex Types]
        
        C2 --> F2[Void, Char, Int, Float, etc.]
        D2 --> G2[Lookup in Symbol Table]
        E2 --> H2[Struct/Union/Enum]
        
        B2 --> I2[merge_base_type]
        I2 --> J2[Handle Signed/Unsigned]
        I2 --> K2[Handle Long/Long Long]
        I2 --> L2[Handle Other Combinations]
        
        I2 --> M2[Final Resolved Type]
        M2 --> N2[Apply Declarator]
        N2 --> O2[Pointer/Array/Function Transformations]
        O2 --> P2[Final Type with Qualifiers]
    end
    
    style TypeResolution fill:#bbf,stroke:#333,stroke-width:2px
    style A2 fill:#ff9,stroke:#333
    style B2 fill:#9f9,stroke:#333
```

## Error Handling Flow

```mermaid
flowchart TD
    subgraph ErrorHandling[Error Handling Process]
        A3[Semantic Violation] --> B3[Create SemanticError]
        B3 --> C3[DuplicateStorageClass]
        B3 --> D3[IllegalTypedefStorage]
        B3 --> E3[MissingBaseType]
        B3 --> F3[InvalidTypeCombination]
        
        B3 --> G3[LowerCtx.report_error]
        G3 --> H3[Convert to Diagnostic]
        G3 --> I3[Add to Error Collection]
        G3 --> J3[Report via DiagnosticEngine]
        
        J3 --> K3[Continue Processing]
        K3 --> L3[Allow Error Recovery]
        K3 --> M3[Report Multiple Errors]
    end
    
    style ErrorHandling fill:#f99,stroke:#333,stroke-width:2px
    style A3 fill:#ff9,stroke:#333
    style B3 fill:#f99,stroke:#333
```

## Symbol Table Integration

```mermaid
flowchart TD
    subgraph SymbolIntegration[Symbol Table Integration]
        A4[Semantic Node Creation] --> B4[create_symbol_entry]
        B4 --> C4[Determine Symbol Kind]
        C4 --> D4[Function Symbol]
        C4 --> E4[Variable Symbol]
        C4 --> F4[Typedef Symbol]
        
        B4 --> G4[Set Type Information]
        B4 --> H4[Set Storage Class]
        B4 --> I4[Set Scope Information]
        
        B4 --> J4[Add to Symbol Table]
        J4 --> K4[Check for Redeclaration]
        J4 --> L4[Handle Scope Management]
        
        L4 --> M4[Global Scope]
        L4 --> N4[Function Scope]
        L4 --> O4[Block Scope]
    end
    
    style SymbolIntegration fill:#9f9,stroke:#333,stroke-width:2px
    style A4 fill:#ff9,stroke:#333
    style B4 fill:#9f9,stroke:#333
```

## Key Data Structures

```mermaid
classDiagram
    class LowerCtx {
        +ast: &mut Ast
        +diag: &mut DiagnosticEngine
        +symbol_table: &mut SymbolTable
        +current_scope: ScopeId
        +errors: ErrorCollection
        +report_error(error: SemanticError, location: SourceSpan)
    }
    
    class DeclSpecInfo {
        +storage: Option~StorageClass~
        +qualifiers: TypeQualifiers
        +base_type: Option~TypeRef~
        +is_typedef: bool
        +is_inline: bool
        +is_noreturn: bool
    }
    
    class SemanticError {
        <<enum>>
        DuplicateStorageClass
        IllegalTypedefStorage
        MissingBaseType
        InvalidTypeCombination
    }
    
    LowerCtx --> DeclSpecInfo : uses
    LowerCtx --> SemanticError : reports
    LowerCtx --> SymbolTable : updates
```

## Process Summary

1. **Input**: Parser AST with `NodeKind::Declaration` nodes
2. **Processing**: Transform declarations into semantic nodes with resolved types
3. **Output**: Semantic AST with `VarDecl`, `FunctionDecl`, `TypedefDecl` nodes
4. **Side Effects**: Updated symbol table with type information
5. **Error Handling**: Comprehensive error reporting with recovery

The semantic lowering phase bridges the gap between the grammar-oriented parser AST and the type-resolved semantic AST, enabling robust type checking and code generation.