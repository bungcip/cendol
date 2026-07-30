## 2024-05-19 - SemanticError::ZeroOrNegativeSizeArray Test Coverage

**Learning:** Adding test coverage for `SemanticError::ZeroOrNegativeSizeArray` on C23 arrays with no elements (e.g. `int arr[] = {};`) hit the targeted code path accurately (`src/semantic/lowering.rs`). Ensuring tests pass correctly using `cargo test -p cendol` verified regressions. It's helpful to remember that `-std=c23` must be enabled to trigger this semantic error constraint.
**Action:** Successfully increased test coverage on C23 empty array behaviors in the compiler without redundant refactoring.

## 2024-11-23 - Memoized Header Resolution Cache

**Learning:** During C compilation/preprocessing, header path resolution is repeatedly queried (e.g. via `#include` directive lookups) resulting in numerous redundant filesystem `exists` (system call) checks, even for files that are already loaded/cached in the compiler. Applying interior-mutable memoization caches (`RefCell<FxHashMap<...>>`) to `HeaderSearch` dramatically avoids these disk I/O operations and speeds up compiling/parsing of large files like SQLite by ~6%.
**Action:** Always consider memoizing filesystem resolution paths and caching directory existence lookups for compilers/preprocessors where static file trees are read repeatedly.

## 2025-02-15 - FxHashMap Type Alias Hashing Constraints in Rust

**Learning:** When using custom hashing in Rust via type aliases (e.g. `use rustc_hash::FxHashMap as HashMap`), calling `HashMap::new()` fallback-resolves to standard library's SipHash-based `RandomState` rather than `FxHasher`, triggering compilation errors on type mismatch. Instead, use `HashMap::default()` to correctly construct maps with the aliased custom hasher. Additionally, swapping standard `hashbrown::HashMap`/`HashSet` to `FxHashMap`/`FxHashSet` in critical passes (e.g. `clif_gen.rs` and `lowering.rs`) where keys are almost exclusively integer-like IDs (e.g. LocalId, TypeId, GlobalId, MirBlockId) drastically reduces hashing overhead.
**Action:** Always use `HashMap::default()` rather than `HashMap::new()` when utilizing type-aliased custom-hash maps, and prioritize `rustc_hash::FxHashMap` for passes processing integer-like compiler IDs.

## 2025-02-23 - FxHashMap for AST and Literal Interning

**Learning:** `hashbrown::HashMap` defaults to the standard library's `SipHash` algorithm for cryptographic DOS resistance, which introduces significant hashing overhead. For performance-critical compiler tables like `LiteralTable` in `src/ast/literal.rs`, literal values (`LitVal`) are interned and searched millions of times during lexing, parsing, and analysis. Replacing `hashbrown::HashMap` with `rustc_hash::FxHashMap` completely removes this SipHash overhead using a fast, non-cryptographic hash function.
**Action:** Always prefer `rustc_hash::FxHashMap` or `rustc_hash::FxHashSet` for global compiler tables, interners, and AST caches where trust of compiled inputs is assumed and micro-optimization is paramount.

## 2025-03-02 - Heap Allocation Avoidance in Struct Packing ABI Lowering
**Learning:** During mid-level IR to Cranelift IR lowering, ABI considerations (specifically function signatures, call arguments, parameters, and returns) repeatedly query whether a structure can be packed into I64/F64 registers. Historically, returning `Option<Vec<Type>>` from packing checks caused continuous heap allocations on the hot compilation path. Returning `Option<smallvec::SmallVec<[Type; 2]>>` instead completely avoids these allocations since packed structs on x86_64 are at most 16 bytes (clamped to at most 2 64-bit registers). Additionally, return value collecting within `Terminator::Return` can be optimized with `smallvec::SmallVec::<[Value; 2]>::new()` instead of a standard `Vec` for small packed aggregate returns.
**Action:** Always prefer stack-allocated collections like `smallvec::SmallVec` for returning array-like values when the maximum capacity is static and small (such as x86_64 register count limits), avoiding heap allocation overhead on hot paths.

## 2025-03-05 - Borrow Checker Lifetime Mitigation via SmallVec in Cranelift Codegen
**Learning:** Returning a slice (such as block parameters from Cranelift `FunctionBuilder::block_params`) and iterating over it can trigger borrow checker errors if the builder is subsequently mutated inside the loop. Cloning with `.to_vec()` satisfies the borrow checker but introduces heap allocations. Instead, collecting or copying the slice into a stack-allocated container like `smallvec::SmallVec<[Value; 8]>` elegantly satisfies the borrow checker with zero heap allocations for the common case where parameter counts are within bounds.
**Action:** Use stack-allocated `SmallVec` or array buffers to satisfy the borrow checker for mutable iterations over lightweight Copy values, completely bypassing `.to_vec()` heap overhead in compiler hot paths.
