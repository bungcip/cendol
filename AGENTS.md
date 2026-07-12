# AGENTS.md — Cendol Compiler Conventions

This document describes the coding conventions and patterns used in the **cendol** C23 compiler so that AI agents can contribute effectively.

## Project Overview

Cendol is a C23 compiler written in Rust (2024 edition) that uses **Cranelift** as its code-generation backend. It follows a traditional multi-phase architecture:

```
C source → Preprocessor → Lexer → Parser → Semantic Analysis → MIR → Cranelift IR → Object Code → Linker
```

## Repository Layout

```
src/
├── main.rs                   # CLI entry point
├── lib.rs                    # Crate root — declares all modules
├── bin/                      # Additional binary utilities
├── ast.rs + ast/             # Flattened AST, literals, dumper, parsed types
├── parser.rs + parser/       # Pratt parser (expressions) + recursive descent
├── pp.rs + pp/               # C11 preprocessor
├── semantic.rs + semantic/   # Analyzer, lowering, types, const eval, conversions
├── mir.rs + mir/             # Mid-level IR definitions, builder, dumper
├── codegen.rs + codegen/     # MIR→Cranelift lowering, object gen, linker
├── diagnostic.rs             # DiagnosticEngine, ParseError, severity levels
├── source_manager.rs         # Source file tracking, SourceSpan, SourceLoc
├── lang_options.rs           # Language standard options
├── driver.rs + driver/       # Compiler driver, custom GCC-style CLI parser, pipeline orchestration
└── tests.rs + tests/         # All unit tests (140+ test files)
```

### Key Dependencies

| Crate                                                 | Purpose                                      |
| ----------------------------------------------------- | -------------------------------------------- |
| `cranelift` / `cranelift-module` / `cranelift-object` | Native code generation                       |
| `cranelift-frontend`                                  | Cranelift IR construction helpers            |
| `insta`                                               | Snapshot testing                             |
| `annotate-snippets`                                   | Rich diagnostic rendering                    |
| `symbol_table`                                        | Interned strings (`NameId` / `GlobalSymbol`) |
| `hashbrown` / `indexmap`                              | Hash maps with serde                         |
| `thiserror`                                           | Error derive macros                          |
| `bitflags`                                            | Type qualifiers, flags                       |
| `smallvec` / `thin-vec`                               | Small-buffer-optimized collections           |
| `log` / `env_logger`                                  | Logging framework                            |
| `target-lexicon`                                      | Target triple parsing                        |
| `serde`                                               | Serialization/Deserialization                |

## Formatting & Linting

| Setting                    | Value       | File                                           |
| -------------------------- | ----------- | ---------------------------------------------- |
| Max line width             | **120**     | `rustfmt.toml`                                 |
| Newline style              | Unix        | `rustfmt.toml`                                 |
| Max function args (clippy) | **8**       | `clippy.toml`                                  |
| `bool_comparison` lint     | **allowed** | `Cargo.toml` (`== false` can be more readable) |

Run `cargo fmt` before committing. Run `cargo clippy` to check for lint issues.

## Visibility Convention

- Use **`pub(crate)`** for most internal APIs (functions, structs, methods).
- Use **`pub`** only for items that need to be exposed outside the crate (driver API, test helpers).
- Module-private items use the default (no visibility modifier).

```rust
// ✅ Preferred
pub(crate) fn visit_ast(...) -> SemanticInfo { ... }

// ✅ Only for truly public API
pub struct CompilerDriver { ... }

// ❌ Avoid making internal helpers pub
pub fn some_internal_helper() { ... }
```

## Two-AST Architecture

Cendol uses a **two-AST architecture** with a lowering phase between them:

```
Parser  →  ParsedAst  →  Semantic Lowering  →  Ast  →  Semantic Analyzer  →  MIR Gen
              ↑                   ↑                ↑
       purely syntactic    resolves types,    type-resolved,
       no symbol lookup    scopes, symbols    enriched with
                                              semantic info
```

### ParsedAst (Syntactic AST)

Defined in `src/ast/parsed.rs`. Produced by the **Parser**. Contains only syntactic information — no type resolution, no symbol lookup, no scope tracking.

```rust
pub struct ParsedAst {
    pub nodes: Vec<ParsedNode>,          // Syntactic nodes
    pub parsed_types: ParsedTypeArena,   // Type syntax storage
}
```

- Uses `ParsedNodeRef` (a `NonZeroU32`) for child references.
- Node kinds are `ParsedNodeKind` — identifiers are just `Ident(NameId)` with no symbol resolution.
- Declarations store raw specifiers (`ThinVec<ParsedDeclSpecifier>`) and declarators (`ParsedDeclarator`).
- Uses `Vec` for variable-length children (e.g., `CompoundStatement(Vec<ParsedNodeRef>)`).

### Ast (Semantic AST)

Defined in `src/ast.rs` + `src/ast/nodes.rs`. Produced by **Semantic Lowering** (`src/semantic/lowering.rs`). Contains resolved types, symbols, and scopes.

```rust
pub struct Ast {
    pub kinds: Vec<NodeKind>,         // Semantic nodes (parallel vectors)
    pub spans: Vec<SourceSpan>,       // Source locations
    pub semantic_info: SemanticInfo,  // Populated after type resolution
}
```

- Uses `NodeRef` (a `NonZeroU32` wrapper) for child references.
- `NodeRef::ROOT` is the translation unit root.
- Access via `ast.get_kind(node)`, `ast.get_span(node)`.
- Identifiers include resolved symbols: `Ident(NameId, SymbolRef)`.
- Declarations are lowered into semantic nodes: `VarDecl`, `FunctionDecl`, `TypedefDecl`, `RecordDecl`, `FieldDecl`, `EnumDecl`.
- Uses `NodeRef` + length for variable-length children (e.g., `CompoundStatement(CompoundStmtData)` with `stmt_start: NodeRef, stmt_len: u16`).
- All data structs derive `Copy` — keeps `NodeKind` small and cache-friendly.
- **Semantic Info**: A side table (parallel vectors and HashMaps) attached after analysis. Contains types, implicit conversions, and value categories.

### Key Differences

| Aspect           | `ParsedAst`                              | `Ast`                                          |
| ---------------- | ---------------------------------------- | ---------------------------------------------- |
| Produced by      | Parser                                   | Semantic Lowering                              |
| Identifiers      | `Ident(NameId)`                          | `Ident(NameId, SymbolRef)`                     |
| Declarations     | `Declaration(ParsedDecl)`                | `VarDecl`, `FunctionDecl`, `TypedefDecl`, etc. |
| Types            | `ParsedType` (syntactic)                 | `QualType` / `TypeRef` (resolved)              |
| Children storage | `Vec<ParsedNodeRef>`                     | `NodeRef` + length (flattened)                 |
| Node data        | Heap-allocated (`Vec`, `Box`, `ThinVec`) | `Copy` structs (cache-friendly)                |
| Scopes           | None                                     | `ScopeId` on scope-bearing nodes               |

### Semantic Lowering (`src/semantic/lowering.rs`)

The `LowerCtx` struct orchestrates the conversion from `ParsedAst` → `Ast`:

- **Type Resolution**: Converts `TypeSpec` → `QualType` via `TypeRegistry`.
- **Symbol Insertion**: Populates `SymbolTable` with resolved declarations.
- **Scope Construction**: Creates and manages `ScopeId` for block/function/file scopes.
- **Declarator Processing**: Recursively applies `ParsedDeclarator` chains (pointers, arrays, functions) to build final types.
- **Constraint Checking**: Enforces C11 rules on storage classes, qualifiers, and declarations.

## Error Handling

### Diagnostic System

- `DiagnosticEngine` collects all errors/warnings as `Diagnostic` structs.
- Errors are NOT panics — compilation continues to report multiple errors.
- Use `annotate-snippets` for rendering with source context.

### Error Types

- **Parse errors**: `ParseError` with `ParseErrorKind` enum (in `diagnostic.rs`).
- **Semantic errors**: `SemanticDiag` with `SemanticError` enum (in `semantic/errors.rs`).
- Each error kind implements `display()` → human-readable message.
- Errors convert to `Vec<Diagnostic>` via `into_diagnostic()` / `IntoDiagnostic` trait.

```rust
// Semantic error reporting pattern
self.report_error(node, SemanticError::NotAnLvalue);
self.report_warning(node, SemanticError::AddressOfArrayAlwaysTrue { name });
```

### ICE (Internal Compiler Error)

Use `unreachable!("ICE: ...")` for impossible states with a descriptive message:

```rust
_ => unreachable!("ICE: Node {:?} does not have a scope", self.get_kind(node_ref)),
```

## MIR (Mid-level IR)

- Defined in `src/mir.rs` with builder pattern in `MirBuilder`.
- Types use `TypeId` indices into a type table.
- Functions contain basic blocks (`MirBlock`) with `MirStmt` and `Terminator`.
- Builder pattern: `builder.add_type(...)`, `builder.define_function(...)`, `builder.create_block(...)`, etc.
- **MirProgram**: Top-level container for all MIR entities.

## Semantic Analyzer Pattern

The semantic analyzer uses a **visitor pattern** with a `SemanticAnalyzer` struct:

```rust
struct SemanticAnalyzer<'a> {
    ast: &'a Ast,
    diag: &'a mut DiagnosticEngine,
    symbol_table: &'a SymbolTable,
    registry: &'a mut TypeRegistry,
    semantic_info: &'a mut SemanticInfo,
    lang_opts: &'a LangOptions,
    source_manager: &'a SourceManager,
    // ... state fields
}
```

- Entry point: `visit_ast(ast, diag, symbol_table, registry, lang_opts, source_manager)` returns a `SemanticInfo`.
- Each node type has a corresponding `visit_*` method.
- Results (types, conversions, value categories) are stored in the `SemanticInfo` side table.
- **Deferred Checks**: Items like `_Static_assert` are often deferred until the end of analysis.
- **Switch Stack**: Uses `SmallVec` to track nested switch statements efficiently.

## Testing Conventions

### Test File Naming

Test files follow the pattern `<phase>_<topic>.rs`:

| Prefix      | Phase                  | Examples                                    |
| ----------- | ---------------------- | ------------------------------------------- |
| `pp_`       | Preprocessor           | `pp_macros.rs`, `pp_conditionals.rs`        |
| `parser_`   | Parser                 | `parser_expr.rs`, `parser_decl.rs`          |
| `semantic_` | Semantic analysis      | `semantic_negative.rs`, `semantic_types.rs` |
| `mir_`      | MIR generation         | `mir_validation.rs`, `mir_gen_sizeof.rs`    |
| `codegen_`  | Code generation        | `codegen_basics.rs`, `codegen_structs.rs`   |
| `driver_`   | Driver/integration     | `driver_ast_dumper.rs`                      |
| `guardian_` | Constraint enforcement | `guardian_bitfield_constraints.rs`          |
| `regr_`     | Regression tests       | `regr_shadowing.rs`, `regr_mixed_sign.rs`   |

### Test Registration

All test modules must be registered in `src/tests.rs`:

```rust
pub mod semantic_negative;
pub mod parser_expr;
```

### Test Helpers (`src/tests/test_utils.rs`)

```rust
// Expect compilation to fail with a specific error message
run_fail_with_message(source, "read-only");

// Expect compilation to fail at a specific phase
run_fail(source, CompilePhase::Mir);

// Expect compilation to succeed
run_pass(source, CompilePhase::Cranelift);

// Expect success with a warning at a specific location
run_pass_with_diagnostic(source, CompilePhase::Mir, "discards qualifiers", 5, 13);

// Expect failure with diagnostic at specific line/col
run_fail_with_diagnostic(source, CompilePhase::Mir, "message", line, col);

// Expect compilation to succeed with a specific C standard
run_pass_with_std(source, CompilePhase::Cranelift, CStandard::C23);

// Expect compilation to fail with a specific C standard and message
run_fail_with_message_and_std(source, "message", CStandard::C23);
```

### Preprocessor Test Helpers (`src/tests/pp_common.rs`)

```rust
assert_pp(source, expected_output)  // Assert that preprocessing matches exactly
check_diag(source, expected_error)  // Assert that preprocessing emits a specific error/warning
```

### Semantic Test Helpers (`src/tests/semantic_common.rs`)

```rust
setup_mir(source)        // Run pipeline to MIR, return MIR dump string
setup_lowering(source)   // Run to lowering, return (Ast, TypeRegistry, SymbolTable)
setup_analysis(source)   // Run full semantic analysis
find_layout(registry, "S")          // Find type layout by name
find_var_decl(ast, "x")             // Find variable declaration in AST
find_enum_constant(symbol_table, "A") // Find enum constant value
```

### Codegen Test Helpers (`src/tests/codegen_common.rs`)

```rust
setup_cranelift(source)           // Compile to Cranelift IR dump string
run_c_code_exit_status(source)    // Compile & run, return exit code
run_c_code_with_output(source)    // Compile & run, return stdout
```

### Snapshot Testing with Insta

Use `insta::assert_yaml_snapshot!` for AST structure and `insta::assert_snapshot!` for text output (like Cranelift IR or MIR dumps):

```rust
#[test]
fn test_simple_addition() {
    let resolved = setup_expr("1 + 2");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - LiteralInt: 1
      - LiteralInt: 2
    ");
}
```

### C Code in Tests

Use raw string literals (`r#"..."#`) for inline C code:

```rust
#[test]
fn test_assignment_to_const() {
    run_fail_with_message(
        r#"
        int main() {
            const int y = 2;
            y = 1;
        }
        "#,
        "read-only",
    );
}
```

### Organizing Test Sections

Use section comments to group related tests within a file:

```rust
// A. Lvalue & Assignment Constraints
#[test]
fn test_assignment_to_const() { ... }

// C. Pointer & Address Semantics
#[test]
fn test_addrof_rvalue() { ... }
```

### Test Design Guidelines

- **Consolidate Tests**: Group small, related test cases into a single `#[test]` function to reduce boilerplate and overhead (e.g., one test function for all invalid `#line` directives).
- **Use Helpers First**: Always prefer phase-specific helpers (like `assert_pp` or `check_diag`) over manual setup (like `setup_pp_with_sm_and_diagnostics`).
- **Regression Placement**: Place small, phase-specific regression tests directly in their corresponding feature test file (e.g., put PP short-circuit tests in `pp_conditionals.rs` instead of a standalone `regr_*.rs` file).

## Compile Phases

The `CompilePhase` enum controls how far the pipeline runs:

```
Preprocessor → Lexer → Parser → SemanticLowering → SemanticAnalysis → Mir → Cranelift → ObjectFile → Link
```

When writing tests, choose the minimum phase needed to validate your assertion.

## Shell Test Scripts

- `realworld_test.py` — Builds and tests real-world C projects (Lua, c-testsuite, libpng).

## Key Design Principles

1. **Flattened data structures** — AST and MIR use index-based references, not tree pointers.
2. **Side tables** — Semantic info is stored in parallel vectors (types, conversions, etc.), not embedded in AST nodes.
3. **Continue on error** — The compiler reports as many errors as possible rather than stopping at the first one.
4. **C11/C23 strict compliance** — Follow standards closely. Constraint violations are tracked in `.jules/guardian.md`.
5. **No K&R style** — Empty parameter lists `int foo()` are treated as `int foo(void)`.
6. **No trigraphs/digraphs** — Not supported; modern C only.
7. **Minimize allocations** — Use `SmallVec`, `Cow`, `Arc<[T]>`, and arena-allocated buffers in hot paths.

## Adding New Features

1. **Parser changes**: Add to the appropriate submodule in `src/parser/`. Update `TokenKind` if new keywords are needed.
2. **AST nodes**: Add new variants to `NodeKind` in `src/ast/nodes.rs`.
3. **Semantic rules**: Add error variants to `SemanticErrorKind` in `src/semantic/errors.rs`, implement checks in `src/semantic/analyzer.rs`.
4. **AST lowering**: Update `src/semantic/lowering.rs` to lower new ParsedAst nodes into AST nodes.
5. **MIR generation**: Update `src/codegen/mir_gen.rs` (`MirGen`) to generate MIR from the new AST nodes.
6. **Code generation**: Update `src/codegen/clif_gen.rs` to handle new MIR constructs.
7. **Tests**: Create test file(s) in `src/tests/`, register in `src/tests.rs`, use the established helpers.

## Running Tests

```bash
# Unit tests (Rust)
cargo test

# With insta snapshot review
cargo insta test

# Real-world project tests (c-testsuite, lua, libpng, etc)
python3 realworld_test.py <project_name>
```

## Running Benchmarks

Cendol uses **Criterion** for performance benchmarking. Benchmarks are located in the `benches/` directory.

### Performance Tracking

When implementing optimizations, use the `compiler_benches` suite to track performance changes in the preprocessor and parser.

```bash
# Run benchmarks (uses SQLite amalgamation as a heavy workload)
cargo bench --bench compiler_benches
```

### Tips for Reliable Benchmarking

1.  **Prepare Data**: Use the `prepare` subcommand to ensure source files are available:
    ```bash
    python3 realworld_test.py prepare sqlite
    ```
2.  **Quiet Environment**: Close heavy background applications (browsers, IDEs) to reduce system noise.
3.  **Statistical Stability**: If results are noisy, increase the `sample_size` in `benches/compiler_benches.rs` (default is 30 for SQLite).
4.  **Baseline Comparison**: Criterion automatically compares results against the last run. "Performance has improved/regressed" messages indicate statistical significance.
5.  **Direct Execution**: Use `run_pipeline()` instead of `run()` in new benchmarks to avoid CLI/IO overhead.

## Cranelift Fork Conventions

Since Cendol maintains a fork of Cranelift (`crates/cranelift`), adhere to the following when modifying it:

1. **Register Allocation Constraints**: 
   - **Never** emit instructions that define or write directly to an allocatable physical register (e.g., `%rax`) before register allocation (such as in ABI lowering `gen_call_setup`). Doing so will cause `regalloc2` to panic. 
   - **Instead**: Load the value into a Virtual Register (`VReg`) using the `VRegAllocator`. To constrain the value to a physical register for a function call, add it to the `uses` array (e.g., passing a `CallArgPair { vreg, preg: regs::rax().into() }`).
2. **Formatting**: 
   - Upstream Cranelift formatting must be preserved. Avoid running `cargo fmt` on `crates/cranelift` using Cendol's root `rustfmt.toml`. Ensure that any `rustfmt.toml` configuration inside `crates/cranelift` exactly mirrors upstream to prevent excessive diffs.
