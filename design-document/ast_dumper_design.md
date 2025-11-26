# AST Dumper Design Document

## Overview

The AST Dumper phase processes the flattened AST and semantic analysis results to generate comprehensive, interactive HTML output for debugging and analysis. It visualizes the compiler's internal representations including the AST structure, symbol tables, scope hierarchy, type information, and diagnostics with rich styling and JavaScript-powered interactivity.

## Responsibilities

- **AST Visualization**: Render the flattened AST as an interactive HTML tree with collapsible nodes
- **Symbol Table Display**: Present symbol information in searchable, cross-referenced tables
- **Scope Hierarchy**: Show scope relationships with navigation and filtering
- **Type Information**: Display canonicalized types with detailed properties
- **Diagnostic Reporting**: Include compiler errors and warnings with source locations
- **Interactive Features**: Provide search, filtering, expand/collapse, and cross-navigation
- **Source Code Integration**: Display original source with syntax highlighting

## Core Data Structures

```rust
/// Configuration for AST dump output
#[derive(Debug, Clone)]
pub struct DumpConfig {
    pub pretty_print: bool,
    pub include_source: bool,
    pub max_depth: Option<usize>,
    pub max_source_lines: Option<usize>,
    pub output_path: PathBuf,
}

impl Default for DumpConfig {
    fn default() -> Self {
        DumpConfig {
            pretty_print: true,
            include_source: false,
            max_depth: None,
            max_source_lines: None,
            output_path: PathBuf::from("ast_dump.html"),
        }
    }
}

/// Main AST dumper that generates HTML visualization
pub struct AstDumper<'src> {
    ast: &'src Ast,
    symbol_table: &'src SymbolTable,
    diag: &'src mut DiagnosticEngine,
    source_manager: &'src mut SourceManager,
    lang_opts: &'src LangOptions,
    target_info: &'src TargetTriple,
    config: DumpConfig,
}
```

## Inputs

The AST Dumper receives comprehensive compiler state:

1. **Flattened AST**: From parser output with semantic annotations
2. **Symbol Table**: From semantic analysis with resolved symbols and scopes
3. **Diagnostic Engine**: Compiler errors, warnings, and notes
4. **Source Manager**: For location information and source code access
5. **Language Options**: C11 compliance settings
6. **Target Information**: Platform-specific details
7. **Dump Configuration**: Output preferences and formatting options

## Output Format

The dumper generates a comprehensive HTML file with:

1. **Embedded CSS**: Extensive styling for professional appearance
2. **JavaScript Interactivity**: Search, filtering, expand/collapse functionality
3. **Multiple Sections**: AST tree, symbol table, scope table, type table, diagnostics
4. **Cross-references**: Clickable links between all related elements
5. **Source Integration**: Syntax-highlighted source code snippets
6. **Responsive Design**: Works on different screen sizes

## HTML Structure

The output includes a complete HTML document with:

- **Header**: Title, embedded CSS styles, and JavaScript functions
- **Navigation**: Table of contents with section links
- **Main Content**: Five major sections with interactive features
- **Footer**: Generation timestamp and configuration info

## Interactive Features

### AST Tree Visualization

The AST is rendered as a hierarchical, collapsible tree:

```html
<div id="ast-tree">
    <ul class="ast-tree">
        <li class="ast-node collapsed" id="node_0">
            <div class="node-content" onclick="toggleAstNode(this)">
                <span class="toggle-icon">▶</span>
                <span class="node-type">TranslationUnit</span>
                <span class="span-info">[main.c:1:1-10:1]</span>
            </div>
            <ul>
                <!-- Child nodes -->
            </ul>
        </li>
    </ul>
</div>
```

**Features:**
- **Collapsible Nodes**: Click to expand/collapse subtrees
- **Source Snippets**: Optional source code display with syntax highlighting
- **Semantic Info**: Type and symbol references with links
- **Search**: Filter nodes by type or content

### Table Sections

Each table provides rich, interactive functionality:

#### Symbol Table
- **Columns**: ID, Name, Kind, Type, Scope, Location
- **Cross-references**: Clickable links to types and scopes
- **Search**: Filter symbols by name or properties
- **Sorting**: Click headers to sort by different criteria

#### Scope Table
- **Hierarchy Display**: Shows parent-child relationships
- **Symbol Lists**: Links to all symbols in each scope
- **Navigation**: Jump between related scopes

#### Type Table
- **Type Details**: Comprehensive type information
- **Qualifiers**: const, volatile, restrict, _Atomic display
- **Size/Alignment**: Computed type properties

#### Diagnostics Table
- **Error Classification**: Color-coded by severity (Error/Warning/Note)
- **Source Links**: Jump to error locations
- **Hints**: Additional suggestions for fixes

## CSS Styling

The dumper includes extensive CSS for professional appearance:

- **Color Scheme**: Professional blue/gray theme
- **Typography**: Clean, readable fonts
- **Layout**: Responsive design with proper spacing
- **Interactive States**: Hover effects and visual feedback
- **Syntax Highlighting**: C language syntax colors
- **Table Styling**: Professional data tables with alternating rows

## JavaScript Functionality

Interactive features powered by embedded JavaScript:

### Tree Controls
```javascript
function expandAllAst() {
    const collapsedNodes = document.querySelectorAll('#ast-tree li.collapsed');
    collapsedNodes.forEach(node => {
        node.classList.remove('collapsed');
        node.classList.add('expanded');
    });
}

function collapseAllAst() {
    const expandedNodes = document.querySelectorAll('#ast-tree li.expanded');
    expandedNodes.forEach(node => {
        node.classList.remove('expanded');
        node.classList.add('collapsed');
    });
}
```

### Search and Filtering
```javascript
function searchAst(query) {
    const lowerQuery = query.toLowerCase();
    const allNodes = document.querySelectorAll('#ast-tree li');

    allNodes.forEach(node => {
        const nodeType = node.querySelector('.node-type');
        const spanInfo = node.querySelector('.span-info');
        const text = (nodeType ? nodeType.textContent : '') +
                    (spanInfo ? spanInfo.textContent : '');

        if (text.toLowerCase().includes(lowerQuery)) {
            node.style.display = '';
            // Expand parent nodes to show results
        } else {
            node.style.display = 'none';
        }
    });
}
```

### Node Type Filtering
```javascript
function filterAstByType(nodeType) {
    const allNodes = document.querySelectorAll('#ast-tree li');

    allNodes.forEach(node => {
        const nodeTypeSpan = node.querySelector('.node-type');
        const nodeTypeText = nodeTypeSpan ? nodeTypeSpan.textContent : '';

        if (!nodeType || nodeTypeText === nodeType) {
            node.style.display = '';
        } else {
            node.style.display = 'none';
        }
    });
}
```

## Implementation Strategy

The dumper uses a comprehensive traversal approach:

1. **HTML Generation**: Builds complete HTML document with all sections
2. **AST Traversal**: Visits each node using index-based navigation
3. **Cross-reference Mapping**: Maintains ID mappings for links between sections
4. **Source Integration**: Retrieves and highlights source code snippets
5. **Table Generation**: Creates searchable, sortable data tables

## Key Features

- **Professional UI**: Extensive CSS styling for compiler-quality output
- **Full Interactivity**: JavaScript-powered search, filtering, and navigation
- **Cross-references**: Bidirectional links between all compiler artifacts
- **Source Integration**: Syntax-highlighted source code with location mapping
- **Comprehensive Coverage**: AST, symbols, scopes, types, and diagnostics
- **Performance**: Efficient generation and rendering for large codebases
- **Accessibility**: Proper HTML structure and keyboard navigation

## Error Handling

The dumper gracefully handles various edge cases:

- **Missing Data**: Shows "unknown" or "unresolved" for incomplete information
- **Invalid References**: Displays broken links with error indicators
- **Large Outputs**: Configurable depth and source line limits
- **Memory Efficiency**: Streaming HTML generation to handle large ASTs

## Integration with Compiler Pipeline

The AST Dumper integrates as the final phase:

- **Input**: Complete compiler state (AST, symbols, diagnostics, sources)
- **Output**: Self-contained HTML file with all assets embedded
- **Configuration**: Command-line flags control output features and limits
- **Error Recovery**: Generates partial output even with compilation errors

This comprehensive visualization tool provides invaluable debugging capabilities for compiler development and user analysis of compilation results.