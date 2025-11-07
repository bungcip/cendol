# Data Flow and Integration Design Document

## Inter-Phase Communication

```mermaid
graph TD
    Preprocessor --> PreprocessedSource[Preprocessed Source];
    PreprocessedSource --> Lexer;
    Lexer --> TokenStream[Token Stream];
    TokenStream --> Parser;
    Parser --> AST[AST];
    AST --> SemanticAnalyzer[Semantic Analysis];
    SemanticAnalyzer --> AnnotatedAST[Annotated AST];
    AnnotatedAST --> ASTDumper[AST Dumper];
```

## Data Structures Between Phases

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