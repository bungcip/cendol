## 2024-05-19 - SemanticError::ZeroOrNegativeSizeArray Test Coverage

**Learning:** Adding test coverage for `SemanticError::ZeroOrNegativeSizeArray` on C23 arrays with no elements (e.g. `int arr[] = {};`) hit the targeted code path accurately (`src/semantic/lowering.rs`). Ensuring tests pass correctly using `cargo test -p cendol` verified regressions. It's helpful to remember that `-std=c23` must be enabled to trigger this semantic error constraint.
**Action:** Successfully increased test coverage on C23 empty array behaviors in the compiler without redundant refactoring.

## 2024-11-23 - Memoized Header Resolution Cache

**Learning:** During C compilation/preprocessing, header path resolution is repeatedly queried (e.g. via `#include` directive lookups) resulting in numerous redundant filesystem `exists` (system call) checks, even for files that are already loaded/cached in the compiler. Applying interior-mutable memoization caches (`RefCell<FxHashMap<...>>`) to `HeaderSearch` dramatically avoids these disk I/O operations and speeds up compiling/parsing of large files like SQLite by ~6%.
**Action:** Always consider memoizing filesystem resolution paths and caching directory existence lookups for compilers/preprocessors where static file trees are read repeatedly.

## 2025-02-15 - FxHashMap Type Alias Hashing Constraints in Rust

**Learning:** When using custom hashing in Rust via type aliases (e.g. `use rustc_hash::FxHashMap as HashMap`), calling `HashMap::new()` fallback-resolves to standard library's SipHash-based `RandomState` rather than `FxHasher`, triggering compilation errors on type mismatch. Instead, use `HashMap::default()` to correctly construct maps with the aliased custom hasher. Additionally, swapping standard `hashbrown::HashMap`/`HashSet` to `FxHashMap`/`FxHashSet` in critical passes (e.g. `clif_gen.rs` and `lowering.rs`) where keys are almost exclusively integer-like IDs (e.g. LocalId, TypeId, GlobalId, MirBlockId) drastically reduces hashing overhead.
**Action:** Always use `HashMap::default()` rather than `HashMap::new()` when utilizing type-aliased custom-hash maps, and prioritize `rustc_hash::FxHashMap` for passes processing integer-like compiler IDs.

## 2025-02-18 - Zero-Allocation Cache Lookup in HeaderSearch

**Learning:** Querying a `HashMap` with keys containing `String` and `PathBuf` typically requires allocating those owned types even for cache lookups, creating significant memory and cpu overhead on hot cache-hit paths. Implementing a custom borrowed query key type (like `SearchKeyRef`) and utilizing `hashbrown`'s `Equivalent` trait allows lookups to be completely allocation-free.
**Action:** Always prefer `Equivalent` trait-based lookups with custom borrowed key types for `HashMap`s used in compiler search or memoization caches.
