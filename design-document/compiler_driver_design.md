# Cendol - C11 Compiler Driver Design Document

## Overview

The Cendol compiler driver orchestrates the entire compilation pipeline, from source file input through preprocessing, lexing, parsing, semantic analysis, and AST dumping. It provides a command-line interface using `clap` for configuration and manages the flow of data between compiler phases.

## Responsibilities

- **CLI Interface**: Parse command-line arguments and configure compilation options
- **Phase Orchestration**: Coordinate execution of all compiler phases in correct order
- **Resource Management**: Handle source file I/O, memory allocation, and cleanup
- **Error Collection**: Aggregate diagnostics from all phases with rich formatting
- **Output Generation**: Direct final output (HTML dumps, error reports) to appropriate destinations
- **Configuration Distribution**: Pass phase-specific options to individual compiler components

## CLI Interface Design

The driver provides a comprehensive command-line interface using the `clap` crate:

```rust
#[derive(Parser, Debug)]
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

    /// Generate HTML AST dump
    #[clap(long)]
    pub dump_ast: bool,

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
/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
}

impl CompilerDriver {
    pub fn new(cli: Cli) -> Self {
        // Initialize with parsed CLI options
        todo!()
    }

    pub fn run(&mut self) -> Result<(), CompilerError> {
        // Execute full compilation pipeline
        todo!()
    }
}
```

## Compilation Pipeline Execution

The driver orchestrates the compilation pipeline with proper error handling and resource management:

```rust
impl CompilerDriver {
    fn compile_file(&mut self, source_path: &Path) -> Result<(), CompilerError> {
        // 1. Load source file through SourceManager
        let source_id = self.source_manager.add_file_from_path(source_path)?;

        // 2. Preprocessing phase
        let preprocessor = Preprocessor::new(&self.source_manager, &self.diagnostics);
        let pp_tokens = preprocessor.process(source_id, &self.config.preprocessor)?;

        // 3. Lexing phase
        let lexer = Lexer::new(&self.source_manager, &self.diagnostics);
        let tokens = lexer.tokenize(&pp_tokens)?;

        // 4. Parsing phase
        let mut ast = Ast::new();
        let parser = Parser::new(&self.source_manager, &self.diagnostics);
        parser.parse(&tokens, &mut ast)?;

        // 5. Semantic analysis phase
        let mut analyzer = SemanticAnalyzer::new(&mut ast, &self.diagnostics);
        analyzer.analyze()?;

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let dumper = AstDumper::new(&ast, &self.config.dump);
            dumper.generate_html()?;
        }

        Ok(())
    }
}
```

## Configuration Management

The driver translates CLI options into a unified configuration structure:

```rust
#[derive(Debug)]
pub struct CompileConfig {
    pub input_files: Vec<PathBuf>,
    pub output_path: Option<PathBuf>,
    pub dump_ast: bool,
    pub verbose: bool,
    pub preprocessor: PreprocessorConfig,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
}

#[derive(Debug)]
pub struct PreprocessorConfig {
    pub max_include_depth: usize,
    pub system_include_paths: Vec<PathBuf>,
}
```

## Error Handling Integration

The driver integrates with the diagnostic system for comprehensive error reporting:

```rust
impl CompilerDriver {
    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = ErrorFormatter {
                show_source: true,
                show_hints: true,
                use_colors: true,
                max_context: 3,
            };

            for diagnostic in &self.diagnostics.errors {
                let formatted = formatter.format_diagnostic(diagnostic, &self.source_manager);
                eprintln!("{}", formatted);
            }

            Err(CompilerError::CompilationFailed)
        } else {
            Ok(())
        }
    }
}
```

## Resource Management

The driver handles all resource lifecycle management:

- **Source File Management**: Loading, caching, and tracking source files
- **Memory Management**: Coordinating arena allocation for AST storage
- **Diagnostic Collection**: Aggregating errors and warnings from all phases
- **Output Generation**: Managing file I/O for HTML dumps and other outputs

## Future Extensions

The driver architecture supports future enhancements:

- **Multiple File Compilation**: Process multiple source files with linking
- **Incremental Compilation**: Track file changes for faster rebuilds
- **Parallel Processing**: Compile independent files concurrently
- **Build System Integration**: Support for make, ninja, and other build tools
- **Code Generation**: Integration with Cranelift for machine code output

## Future Considerations

- **Multiple Input Files**: Support compiling multiple C source files and linking them.
- **Linker Integration**: Integrate with a linker to produce executable binaries.
- **Intermediate Representation (IR) Generation**: Add phases for generating Cranelift IR or other intermediate representations.
- **Optimization Passes**: Implement various optimization passes on the IR.
- **Target-Specific Code Generation**: Support different target architectures and operating systems.
- **Build System Integration**: Provide options for integration with build systems like Make or Cargo.
- **Incremental Compilation**: Explore techniques for faster recompilation of changed files.