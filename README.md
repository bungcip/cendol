# Cendol

Cendol is a C11 compiler implemented in Rust. It is a learning project to understand the process of building a compiler from scratch, focusing on high-performance compiler architecture and comprehensive C11 standard compliance.

## Features

* **Full C11 Preprocessor**: Complete preprocessor with macro expansion, conditional compilation, file inclusion, and built-in macros (`__FILE__`, `__LINE__`, etc.)
* **Lexer**: Tokenization of C11 source code with proper handling of literals, keywords, and operators
* **Parser**: Comprehensive C11 syntax parsing using Pratt parsing for expressions and recursive descent for statements
* **Semantic Analysis**: Type checking, symbol resolution, and semantic validation
* **Code Generation**: Compiles to native object code using Cranelift backend
* **Linker Integration**: Automatic invocation of system linker (clang) to produce executables
* **Rich Diagnostics**: Error reporting with source location tracking

## Architecture

Cendol follows a traditional multi-phase compiler architecture optimized for performance:

1. **Preprocessing Phase**: Transforms C source with macro expansion and includes
2. **Lexing Phase**: Converts preprocessed tokens to lexical tokens
3. **Parsing Phase**: Builds a flattened Abstract Syntax Tree (AST)
4. **Semantic Analysis Phase**: Performs type checking and symbol resolution
5. **MIR Generation**: Lowers AST to Mid-level Intermediate Representation
6. **Code Generation**: Generates native machine code via Cranelift
7. **Linking**: Links object files to create the final executable

## Getting Started

### Prerequisites

* Rust 2024 edition or later
* Cargo
* Clang (used as the system linker)

### Building

To build the compiler, run:

```bash
cargo build
```

For release build with optimizations:

```bash
cargo build --release
```

### Usage

To compile a C file to an executable:

```bash
cargo run -- -o <output_file> <input_file>
```


#### Other Options

* `-E`: Preprocess only, output preprocessed source to stdout
* `-P`: Suppress line markers in preprocessor output
* `-C`: Retain comments in preprocessor output
* `-I <path>`: Add include search path
* `-D <name>[=<value>]`: Define preprocessor macro
* `--verbose`: Enable verbose diagnostic output

#### Examples

Preprocess a file:
```bash
cargo run -- -E test.c
```


Define macros and include paths:
```bash
cargo run -- -D DEBUG=1 -I /usr/include test.c
```

## Design Documents

Comprehensive design documentation is available in the [`design-document/`](design-document/) directory:

* [Main Architecture](design-document/main.md) - Overall compiler design and goals
* [Preprocessor Design](design-document/preprocessor_design.md) - Preprocessing phase details
* [Lexer Design](design-document/lexer_design.md) - Tokenization strategy
* [Parser Design](design-document/parser_design.md) - AST construction
* [Semantic Analysis](design-document/semantic_analysis_design.md) - Type checking and validation

## Contributing

This is a learning project, but contributions are welcome! Areas of interest include:

* Additional C11 language features
* Performance optimizations
* Testing and bug fixes
* Documentation improvements

## AI-Friendly Contributions

This project is AI-friendly and welcomes contributions from developers using AI tools. We encourage the use of AI for code generation, debugging, and documentation to enhance productivity.

## License

See [LICENSE](LICENSE) file for details.
