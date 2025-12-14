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

    /// Suppress line markers in preprocessor output
    #[clap(short = 'P')]
    pub suppress_line_markers: bool,

    /// Retain comments in preprocessor output
    #[clap(short = 'C', long = "retain-comments")]
    pub retain_comments: bool,

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
    pub preprocessor: crate::pp::PPConfig,
    pub suppress_line_markers: bool,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
}

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
    output_handler: OutputHandler,
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
        log::debug!("Starting compilation of file: {}", source_path.display());
        let lang_options = LangOptions::c11();
        let target_triple = Triple::host();

        // 1. Load source file through SourceManager
        let source_id = self
            .source_manager
            .add_file_from_path(source_path)
            .map_err(|e| CompilerError::IoError(format!("Failed to read {}: {}", source_path.display(), e)))?;

        // 2. Preprocessing phase
        let pp_tokens = {
            let mut preprocessor = Preprocessor::new(
                &mut self.source_manager,
                &mut self.diagnostics,
                lang_options.clone(),  // TODO: make it to just borrow
                target_triple.clone(), // TODO: make it to just borrow
                &self.config.preprocessor,
            );

            // Preprocessor is dropped here, releasing the borrow on diagnostics
            match preprocessor.process(source_id, &self.config.preprocessor) {
                Ok(t) => t,
                Err(e) => {
                    if self.diagnostics.has_errors() {
                        return Ok(());
                    } else {
                        return Err(CompilerError::PreprocessorError(format!(
                            "Preprocessing failed: {:?}",
                            e
                        )));
                    }
                }
            }
        };

        // Check for preprocessing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // If preprocess only, dump the preprocessed output
        if self.config.preprocess_only {
            self.output_handler.dump_preprocessed_output(
                &pp_tokens,
                self.config.suppress_line_markers,
                &self.source_manager,
            )?;
            return Ok(());
        }

        // 3. Lexing phase
        let tokens = {
            let mut lexer = Lexer::new(&pp_tokens);

            // Lexer is dropped here, releasing the borrow on diagnostics
            lexer.tokenize_all()
        };

        // Check for lexing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // 4. Parsing phase
        let mut ast = {
            let mut temp_ast = Ast::new();
            {
                let mut parser = Parser::new(&tokens, &mut temp_ast, &mut self.diagnostics);
                if let Err(e) = parser.parse_translation_unit() {
                    // Report the error but continue with empty AST
                    self.diagnostics.report_parse_error(e);
                }
                // Parser is dropped here, releasing the borrow on diagnostics
            }
            // Return the AST for use in next phases
            temp_ast
        };

        // Check for parsing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // print parser AST to check
        if self.config.dump_parser {
            self.output_handler.dump_parser(&ast);
            return Ok(());
        }

        // 5. Semantic analysis phase
        let symbol_table = {
            let mut analyzer = SemanticAnalyzer::new(&mut ast, &mut self.diagnostics);
            let _semantic_output = analyzer.analyze();
            // Analyzer is dropped here, releasing the borrow on diagnostics
            // We need to restructure to get the symbol table out
            // For now, we'll create a new empty one and move the data
            let mut new_table = SymbolTable::new();
            std::mem::swap(&mut new_table, &mut analyzer.symbol_table);
            new_table
        };

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let mut args = AstDumpArgs {
                ast: &ast,
                symbol_table: &symbol_table,
                diagnostics: &mut self.diagnostics,
                source_manager: &mut self.source_manager,
                lang_options: &lang_options,
                target_triple: &target_triple,
            };
            self.output_handler.dump_ast(&mut args, &self.config)?;
        }

        Ok(())
    }
}
```

## Configuration Management

The driver translates CLI options into a unified configuration structure with proper defaults:

```rust
impl Cli {
    /// Convert CLI arguments into compilation configuration
    pub fn into_config(self) -> CompileConfig {
        // Parse defines
        let defines = self
            .defines
            .iter()
            .map(|def| {
                if let Some(eq_pos) = def.find('=') {
                    let name = def[..eq_pos].to_string();
                    let value = Some(def[eq_pos + 1..].to_string());
                } else {
                    (def.clone(), None)
                }
            })
            .collect();

        CompileConfig {
            input_files: self.input_files,
            output_path: self.output,
            dump_ast: self.dump_ast,
            dump_parser: self.dump_parser,
            preprocess_only: self.preprocess_only,
            verbose: self.verbose,
            preprocessor: crate::pp::PPConfig {
                max_include_depth: self.preprocessor.max_include_depth,
                ..Default::default()
            },
            suppress_line_markers: self.suppress_line_markers,
            include_paths: self.include_paths,
            defines,
        }
    }
}
```

## Error Handling Integration

The driver integrates with the diagnostic system for comprehensive error reporting:

```rust
impl CompilerDriver {
    /// Report any accumulated errors
    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();
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