# Cendol

Cendol is a C compiler implemented in Rust. It is a learning project to understand the process of building a compiler from scratch.

## Features

* C preprocessor with macro expansion and conditional compilation.
* Parser for a subset of the C language.
* Code generation to object files using Cranelift.

## Getting Started

### Prerequisites

* Rust and Cargo
* A C compiler like GCC or Clang for linking

### Building

To build the compiler, run the following command:

```
cargo build
```

### Usage

To compile a C file, run the following command:

```
cargo run -- <input_file> [options]
```

#### Options

* `-o <output_file>`: Specify the output file name.
* `-c`: Compile only, do not link.
* `-E`: Preprocess only.
* `-D<macro>[=<value>]`: Define a macro.
* `-I<path>`: Add an include path.
* `--wall`: Enable all warnings.
* `--verbose`: Verbose output.
