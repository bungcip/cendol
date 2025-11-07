# AST Dumper Design Document

## Overview

The AST Dumper phase processes the flattened AST and semantic analysis results to generate human-readable HTML output for debugging and analysis. It visualizes the compiler's internal representations including the AST structure, symbol tables, scope hierarchy, and type information.

## Responsibilities

- **AST Visualization**: Render the flattened AST as an interactive HTML tree structure
- **Symbol Table Display**: Present symbol information in tabular format with cross-references
- **Scope Hierarchy**: Show scope relationships and symbol ownership
- **Type Information**: Display canonicalized types with their properties
- **Cross-referencing**: Enable navigation between related elements (AST nodes ↔ symbols ↔ types)

## Core Data Structures

```rust
/// Main AST dumper
pub struct AstDumper<'src> {
    ast: &'src Ast,
    symbol_table: &'src SymbolTable,
    diag: &'src DiagnosticEngine,
    config: DumpConfig,
}

/// Configuration for dump output
pub struct DumpConfig {
    pub pretty_print: bool,
    pub include_source: bool,
    pub max_depth: Option<usize>,
    pub output_path: PathBuf,
}
```

## Inputs

The AST Dumper receives:

1. **Flattened AST**: From parser output with semantic annotations
2. **Symbol Table**: From semantic analysis with resolved symbols
3. **Source Manager**: For location information and source code access
4. **Dump Configuration**: Output preferences and formatting options

## Output Format

The dumper generates a single HTML file with embedded CSS and optional JavaScript for interactivity. The output includes:

1. **AST Tree View**: Hierarchical visualization of the flattened AST using nested lists
2. **Symbol Table**: Tabular display of all symbols with cross-references
3. **Scope Table**: Scope hierarchy and symbol ownership
4. **Type Table**: Canonicalized types with properties and relationships

## HTML Structure

```html
<!DOCTYPE html>
<html>
<head>
    <title>Cendol AST Dump</title>
    <style>
        /* Embedded CSS for styling */
        .ast-node { margin: 5px; }
        .node-type { font-weight: bold; color: #2E86AB; }
        .semantic-info { background: #F8F9FA; padding: 5px; margin: 5px; }
        table { border-collapse: collapse; width: 100%; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    </style>
</head>
<body>
    <h1>Cendol Compiler AST Dump</h1>

    <section id="ast-section">
        <h2>Abstract Syntax Tree</h2>
        <div id="ast-tree"><!-- AST content --></div>
    </section>

    <section id="symbols-section">
        <h2>Symbol Table</h2>
        <table id="symbol-table"><!-- Symbol table content --></table>
    </section>

    <section id="scopes-section">
        <h2>Scope Table</h2>
        <table id="scope-table"><!-- Scope table content --></table>
    </section>

    <section id="types-section">
        <h2>Type Table</h2>
        <table id="type-table"><!-- Type table content --></table>
    </section>
</body>
</html>
```

## AST Tree Visualization

The flattened AST is rendered as a hierarchical HTML structure using nested `<ul>` and `<li>` elements. Each node displays:

- **Node Kind**: The AST node type (e.g., `FunctionDef`, `BinaryOp`, `Ident`)
- **Source Span**: Location information in the original source
- **Semantic Information**: Resolved types, symbol references, constant values
- **Child Nodes**: Nested subtrees for complex expressions/statements

**Example Output:**
```html
<ul class="ast-tree">
    <li class="ast-node">
        <span class="node-type">TranslationUnit</span>
        <span class="span-info">[main.c:1:1-10:1]</span>
        <ul>
            <li class="ast-node">
                <span class="node-type">FunctionDef</span>
                <span class="span-info">[main.c:3:1-9:1]</span>
                <div class="semantic-info">
                    Type: <a href="#type_1">int(void)</a>,
                    Symbol: <a href="#sym_1">main</a>
                </div>
                <!-- Function body nodes -->
            </li>
        </ul>
    </li>
</ul>
```

## Table Representations

### Symbol Table
Displays all symbols with their properties and cross-references:

| Column | Description |
|--------|-------------|
| ID | Unique symbol identifier |
| Name | Symbol name (resolved via GlobalSymbol) |
| Kind | Variable, Function, Typedef, etc. |
| Type | Link to type table entry |
| Scope | Link to scope table entry |
| Location | Source location |

### Scope Table
Shows scope hierarchy and relationships:

| Column | Description |
|--------|-------------|
| ID | Unique scope identifier |
| Parent | Parent scope (if any) |
| Kind | Global, Function, Block, etc. |
| Level | Nesting depth |
| Symbols | Links to symbols in this scope |

### Type Table
Presents canonicalized types with their properties:

| Column | Description |
|--------|-------------|
| ID | Unique type identifier |
| Kind | Primitive, Pointer, Array, Function, etc. |
| Base | Base type (for derived types) |
| Qualifiers | const, volatile, restrict, _Atomic |
| Size | Type size in bytes |
| Details | Additional type-specific information |

## Implementation Strategy

The dumper uses a visitor pattern to traverse the flattened AST and generate HTML output:

1. **AST Traversal**: Visits each node in the flattened array using index-based navigation
2. **HTML Generation**: Builds HTML strings with proper escaping and formatting
3. **Cross-reference Resolution**: Maintains mappings between AST nodes, symbols, and types
4. **Source Integration**: Optionally includes source code snippets for context

## Features

- **Interactive Navigation**: Clickable links between AST nodes and symbol/type definitions
- **Collapsible Trees**: JavaScript-powered expand/collapse for large AST structures
- **Search Functionality**: Filter symbols, types, and scopes by name or properties
- **Source Code Integration**: Display original source code alongside AST representation
- **Responsive Design**: Mobile-friendly HTML layout

## Error Handling

The dumper gracefully handles incomplete or malformed compiler output:

- **Missing Information**: Displays "unknown" or "unresolved" for missing data
- **Invalid References**: Shows broken links with clear error indicators
- **Truncation**: Limits output size for very large programs with configurable depth limits

## Performance Optimizations

- **Streaming HTML Generation**: Avoids building large strings in memory
- **Lazy Evaluation**: Only computes expensive representations when needed
- **Memory-efficient**: Reuses string buffers and minimizes allocations
- **Scalable**: Handles large codebases through pagination and virtual scrolling

## Integration with Compiler Pipeline

The AST Dumper receives the final compiler state and generates debug output:

- **Input**: `Ast`, `SymbolTable`, `SourceManager`, and `DumpConfig`
- **Output**: Single HTML file with embedded CSS and JavaScript
- **Configuration**: Controlled by compiler flags for different output verbosity levels