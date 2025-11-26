# Cendol - C11 Compiler Driver Design Document

## Overview

The Cendol compiler driver orchestrates the entire compilation pipeline, from source file input through preprocessing, lexing, parsing, semantic analysis, and AST dumping. It provides a command-line interface using `clap` for configuration and manages the flow of data between compiler phases with proper error handling and resource management.

## Responsibilities

- **CLI Interface**: Parse command-line arguments and configure compilation options
- **Phase Orchestration**: Coordinate execution of all compiler phases in correct order with error checking
- **Resource Management**: Handle source file I/O, memory allocation, and cleanup with proper borrowing
- **Error Collection**: Aggregate diagnostics from all phases with rich formatting
- **Output Generation**: Direct final output (HTML dumps, preprocessed source, parser dumps) to appropriate destinations
- **Configuration Distribution**: Pass phase-specific options to individual compiler components

## CLI Interface Design

The driver provides a comprehensive command-line interface using the `clap` crate:

```rust
#[derive(CliParser, Debug)]
#[clap(name = "cendol", about = "C11 Compiler written in Rust")]
pub struct Cli {
    /// Input C source files
    #[clap(value_parser, required = true)]
    pub input_files: Vec<PathBuf>,

    /// Output file for AST dump
    #[clap(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// Enable verbose diagnostic output
    #[clap(short, long)]
    pub verbose: bool,

    /// Dump parser state (for debugging)
    #[clap(long)]
    pub dump_parser: bool,

    /// Generate HTML AST dump
    #[clap(long)]
    pub dump_ast: bool,

    /// Preprocess only, output preprocessed source to stdout
    #[clap(short = 'E')]
    pub preprocess_only: bool,

    /// Preprocessor options
    #[clap(flatten)]
    pub preprocessor: PreprocessorOptions,

    /// Include search paths
    #[clap(short = 'I', long = "include-path", value_name = "DIR", action = clap::ArgAction::Append)]
    pub include_paths: Vec<PathBuf>,

    /// Preprocessor macro definitions
    #[clap(short = 'D', long = "define", value_name = "NAME[=VALUE]", action = clap::ArgAction::Append)]
    pub defines: Vec<String>,
}

#[derive(Args, Debug)]
pub struct PreprocessorOptions {
    /// Maximum include depth
    #[clap(long, default_value = "100")]
    pub max_include_depth: usize,
}
```

## Core Driver Architecture

```rust
/// Configuration for compilation
#[derive(Debug)]
pub struct CompileConfig {
    pub input_files: Vec<PathBuf>,
    pub output_path: Option<PathBuf>,
    pub dump_ast: bool,
    pub dump_parser: bool,
    pub preprocess_only: bool,
    pub verbose: bool,
    pub preprocessor: PreprocessorConfig,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
}

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
}
```

## Compilation Pipeline Execution

The driver orchestrates the compilation pipeline with proper error handling and resource management:

```rust
impl CompilerDriver {
    pub fn run(&mut self) -> Result<(), CompilerError> {
        // Process each input file
        for input_file in self.config.input_files.clone() {
            self.compile_file(&input_file)?;
        }

        // Report errors if any
        self.report_errors()?;

        Ok(())
    }

    fn compile_file(&mut self, source_path: &Path) -> Result<(), CompilerError> {
        // 1. Load source file through SourceManager
        let source_id = self.source_manager.add_file_from_path(source_path)?;

        // 2. Preprocessing phase
        let pp_tokens = {
            let mut preprocessor = Preprocessor::new(/* ... */);
            preprocessor.process(source_id, &self.config.preprocessor)?
        };

        // Stop if preprocessing errors
        if self.diagnostics.has_errors() { return Ok(()); }

        // Preprocess-only mode
        if self.config.preprocess_only {
            self.dump_preprocessed_output(&pp_tokens)?;
            return Ok(());
        }

        // 3. Lexing phase
        let tokens = {
            let mut lexer = Lexer::new(/* ... */);
            lexer.tokenize_all()
        };

        // Stop if lexing errors
        if self.diagnostics.has_errors() { return Ok(()); }

        // 4. Parsing phase
        let mut ast = {
            let mut parser = Parser::new(/* ... */);
            parser.parse_translation_unit()?;
            // Parser dropped here, releasing borrow
        };

        // Stop if parsing errors
        if self.diagnostics.has_errors() { return Ok(()); }

        // Parser dump mode
        if self.config.dump_parser {
            self.dump_parser(&ast);
            return Ok(());
        }

        // 5. Semantic analysis phase
        let symbol_table = {
            let mut analyzer = SemanticAnalyzer::new(/* ... */);
            analyzer.analyze();
            // Extract symbol table from analyzer
            let mut new_table = SymbolTable::new();
            std::mem::swap(&mut new_table, &mut analyzer.symbol_table);
            new_table
        };

        // Stop if semantic errors
        if self.diagnostics.has_errors() { return Ok(()); }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let dump_config = DumpConfig { /* ... */ };
            let mut dumper = AstDumper::new(/* ... */);
            let html = dumper.generate_html()?;
            fs::write(&output_path, html)?;
        }

        Ok(())
    }
}
```

## Configuration Management

The driver translates CLI options into a unified configuration structure with proper defaults:

```rust
impl CompilerDriver {
    pub fn new(cli: Cli) -> Result<Self, String> {
        // Parse macro definitions (NAME[=VALUE])
        let defines = cli.defines.iter().map(|def| {
            if let Some(eq_pos) = def.find('=') {
                let name = def[..eq_pos].to_string();
                let value = Some(def[eq_pos + 1..].to_string());
                (name, value)
            } else {
                (def.clone(), None)
            }
        }).collect();

        let config = CompileConfig {
            input_files: cli.input_files,
            output_path: cli.output,
            dump_ast: cli.dump_ast,
            dump_parser: cli.dump_parser,
            preprocess_only: cli.preprocess_only,
            verbose: cli.verbose,
            include_paths: cli.include_paths,
            defines,
            preprocessor: PreprocessorConfig {
                max_include_depth: cli.preprocessor.max_include_depth,
                system_include_paths: vec![
                    PathBuf::from("/usr/lib/gcc/x86_64-linux-gnu/13/include"),
                    PathBuf::from("/usr/local/include"),
                    PathBuf::from("/usr/include/x86_64-linux-gnu"),
                    PathBuf::from("/usr/include"),
                ],
            },
        };

        Ok(CompilerDriver {
            config,
            diagnostics: DiagnosticEngine::new(),
            source_manager: SourceManager::new(),
        })
    }
}
```

## Error Handling Integration

The driver integrates with the diagnostic system for comprehensive error reporting:

```rust
impl CompilerDriver {
    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = ErrorFormatter::default();
            formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
            return Err(CompilerError::CompilationFailed);
        }
        Ok(())
    }
}
```

## Special Output Modes

### Preprocessing Only (`-E`)

Outputs the preprocessed source to stdout:

```rust
fn dump_preprocessed_output(&self, pp_tokens: &[PPToken]) -> Result<(), CompilerError> {
    for token in pp_tokens {
        if token.kind == PPTokenKind::Eof { break; }
        print!("{}", token.get_text());
    }
    println!();
    Ok(())
}
```

### Parser Debugging (`--dump-parser`)

Dumps the raw AST structure for parser debugging:

```rust
fn dump_parser(&self, ast: &Ast) {
    for (i, node) in ast.nodes.iter().enumerate() {
        if matches!(node.kind, NodeKind::Dummy) { continue; }
        print!("{}: ", i + 1);
        self.dump_parser_kind(&node.kind);
    }
}
```

## Resource Management

The driver handles all resource lifecycle management with careful borrowing patterns:

- **Source File Management**: Loading, caching, and tracking source files through `SourceManager`
- **Memory Management**: Scoped borrowing to allow phases to release resources between steps
- **Diagnostic Collection**: Aggregating errors and warnings from all phases
- **Output Generation**: Managing file I/O for HTML dumps and other outputs
- **Phase Isolation**: Each phase borrows resources temporarily, allowing clean separation

## Future Extensions

The driver architecture supports future enhancements:

- **Multiple File Compilation**: Process multiple source files with linking
- **Incremental Compilation**: Track file changes for faster rebuilds
- **Parallel Processing**: Compile independent files concurrently
- **Build System Integration**: Support for make, ninja, and other build tools
- **Code Generation**: Integration with Cranelift for machine code output
- **Optimization Pipeline**: Add optimization passes between semantic analysis and code generation

## Implementation Notes

- **Borrowing Pattern**: Uses scoped blocks to release borrows between phases
- **Error Propagation**: Stops processing current file on errors but continues with other files
- **Configuration Parsing**: Handles complex CLI options like macro definitions with `=`
- **System Integration**: Includes standard system include paths for typical Linux environments
- **Debugging Support**: Multiple dump modes for different development needs