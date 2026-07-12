# Rust Environment and Tooling

## Overview

Cendol is developed using the latest stable Rust toolchain (Rust 2024 edition). The project leverages the unique strengths of Rust—memory safety, zero-cost abstractions, and a powerful build system—to build a robust C23 compiler.

## Key Dependencies

The project carefully selects high-quality crates to handle specialized tasks:

| Crate | Purpose |
| :--- | :--- |
| **Cranelift** | High-performance backend for code generation. |
| **symbol_table** | Fast and thread-safe string interning. |
| **bitflags** | Efficient bit-field representation for flags (e.g., storage classes). |
| **thiserror** | Minimalist error deriving for internal errors. |
| **annotate-snippets**| Rich diagnostic rendering. |
| **bumpalo** | Fast arena-style allocation. |
| **hashbrown** | Performance-optimized hash maps. |

## Tooling Integration

### 1. `cargo`
The heart of the development workflow. Cendol is structured as a single workspace containing multiple modules.

### 2. `rustfmt` and `clippy`
Cendol maintains strict linting and formatting rules enforced through CI. We use a customized `rustfmt.toml` with a wider line limit (120) to accommodate complex Rust match statements and logic.

### 3. `insta` (Snapshots)
We use `insta` for regression testing of AST, MIR, and Codegen output. This ensures that refactorings don't change the compiler's output unknowingly.

## Target Support

Cendol aims to be a cross-compiler.
- **Host**: Linux, macOS, Windows (using WSL/Ubuntu).
- **Target**: Initially `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`.
- **Linker**: Relies on system-installed `clang` or `gcc` as the linker driver.

## Project Structure

```text
src/
  pp/               # Preprocessor implementation
  parser/           # Pratt and recursive descent parser
  ast/              # Two-stage AST definitions
  semantic/         # Lowering and analysis logic
  mir/              # Mid-level IR and validation
  codegen/          # Cranelift lowering and linker integration
  driver/           # CLI and pipeline orchestration
  diagnostic.rs     # Diagnostic engine
  source_manager.rs # File and buffer management
```