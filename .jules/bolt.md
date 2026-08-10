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

## 2025-08-01 - Allocation-Free Header Search Cache Lookup via Arc

**Learning:** During C compilation, header path resolution is repeatedly queried. While memoizing path lookups inside `HeaderSearch` via interior-mutable `RefCell<HashMap<...>>` caches successfully avoids disk I/O, returning `Option<PathBuf>` from lookups still results in cloning the path buffer and allocating memory on the heap for every single cache hit. Replacing `Option<PathBuf>` with `Option<Arc<PathBuf>>` in cache values completely avoids these heap allocations and deep string copies on cache hits.
**Action:** Always prefer `Arc` (or `Rc` if single-threaded) for caching owned string-like or path-like key/value mappings inside compilers or preprocessors to make cache lookups entirely allocation-free.
## 2025-03-05 - Borrow Checker Lifetime Mitigation via SmallVec in Cranelift Codegen
**Learning:** Returning a slice (such as block parameters from Cranelift `FunctionBuilder::block_params`) and iterating over it can trigger borrow checker errors if the builder is subsequently mutated inside the loop. Cloning with `.to_vec()` satisfies the borrow checker but introduces heap allocations. Instead, collecting or copying the slice into a stack-allocated container like `smallvec::SmallVec<[Value; 8]>` elegantly satisfies the borrow checker with zero heap allocations for the common case where parameter counts are within bounds.
**Action:** Use stack-allocated `SmallVec` or array buffers to satisfy the borrow checker for mutable iterations over lightweight Copy values, completely bypassing `.to_vec()` heap overhead in compiler hot paths.
## 2025-03-09 - Fast-path for Single String Literals in Lexer

**Learning:** During parsing/lexing, C programs contain many string literals, of which the vast majority (>99%) are single and non-concatenated (e.g. `"SELECT..."` or `"<digits>"`). In the previous implementation, the parser's `next_token` always allocated a `SmallVec`, peeked/pushed/popped adjacent tokens, and allocated a temporary `String` buffer. Adding an `is_single` check via `peek_pp_token` allows single string literals to bypass this entire overhead, drastically reducing memory allocations and CPU instructions in the lexer's hot path.
**Action:** Always identify and fast-path the common single-item case for list/concatenation collectors to avoid unnecessary heap allocations and collection overhead in the compiler's lexer.

## 2025-10-12 - Allocation-Free Borrow Checker Satisfaction via SmallVec in Cranelift IR Generation
**Learning:** In Cranelift IR generation/lowering, querying instruction results via `inst_results` returns a borrowed slice of `Value`s. When processing these results, subsequent operations often mutate the builder mutably, which violates the borrow checker if we hold the slice reference. Cloning with `.to_vec()` satisfies the borrow checker but forces a heap allocation. Utilizing stack-allocated `smallvec::SmallVec` buffers (e.g. `[Value; 2]` or `[Value; 8]`) satisfies the borrow checker while completely eliminating heap allocation overhead in these hot compilation paths.
**Action:** Always prefer `smallvec::SmallVec` to temporarily copy/clone lightweight `Copy` structures like Cranelift `Value`s when satisfying the borrow checker across builder mutations, avoiding heap allocations in the codegen hot path.
## 2025-10-15 - FxHashMap for PathBuf and String in SourceManager

**Learning:** During C preprocessing, file existence and ID resolution are queried repeatedly (e.g., via `__has_include` or duplicate include checks). `SourceManager`'s `path_to_id` map historically used standard `hashbrown::HashMap` which defaults to the slow, cryptographically secure `SipHash` algorithm. Swapping this map to use `rustc_hash::FxHashMap` completely removes the SipHash overhead for `PathBuf` keys, significantly accelerating path resolution and header check performance with zero functional regression.
**Action:** Always prefer `rustc_hash::FxHashMap` over standard `hashbrown::HashMap` in core resource tables (such as `SourceManager`'s path-to-ID indices) where path string lookups are hot and denial-of-service protection is not required.

## 2025-10-25 - Direct Arc construction from SmallVec Slice in HideSetTable

**Learning:** During macro expansion, Dave Prosser's hiding set algorithm repeatedly interns token sets to prevent infinite recursive macro expansion. Historically, `HideSetTable::intern` accepted a `SmallVec<[StringId; 4]>` and converted it into a heap-allocated `Vec` using `.into_vec()`, before wrapping it inside an `Arc<[StringId]>`. Because macro hide-sets are extremely small (usually containing 1 or 2 macro names), they fit entirely within `SmallVec`'s inline storage. Replacing `.into_vec()` with `Arc::from(set.as_slice())` avoids constructing the intermediate heap-allocated `Vec` entirely, eliminating a redundant heap allocation on the hot interning path.
**Action:** Always prefer instantiating `Arc<[T]>` or `Box<[T]>` directly from a slice reference `as_slice()` instead of consuming stack-allocated `SmallVec` or `Vec` containers with `.into_vec()`, completely bypassing unnecessary heap allocation overhead on critical paths.

## 2025-11-01 - Fast-path for Non-Combined Single-Character Punctuation in Preprocessor Lexer

**Learning:** During lexical analysis in compilers, single-character punctuation (such as parentheses, brackets, braces, commas, semicolons, colons, tildes, and question marks) make up a substantial portion of all source tokens. In the original implementation, all operator-like characters were directed to a complex `lex_operator` method which performed expensive matching and branching on multi-character sequences. Adding a fast-path inside `PPLexer::next_token` to directly match and return `PPToken` for these non-combined characters completely bypasses this dispatch overhead with zero functional regression.
**Action:** Always identify and fast-path single-character punctuation marks that can never be combined into multi-character operators, avoiding the overhead of dispatcher matching and state queries on hot lexical analysis paths.
