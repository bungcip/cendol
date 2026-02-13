## 2024-07-25 - Two-Pass Allocation for Sequential Items
**Learning:** A common performance anti-pattern in this codebase is processing a peekable iterator in a single pass, where an intermediate collection (like a `String` or `Vec`) is built up, leading to multiple costly reallocations.
**Action:** For future optimizations involving sequential item processing, I will favor a two-pass approach. First, iterate (or peek ahead) to calculate the final required capacity. Second, perform a single allocation with `with_capacity`. Third, iterate again to populate the collection. This avoids N reallocations, providing a significant performance improvement.

## 2026-01-31 - Path Comparison and Loop Invariant Hoisting
**Learning:** Calling `format!` and `to_string_lossy()` inside a hot loop (like `is_recursive_expansion`) is a major performance bottleneck due to repeated heap allocations. Direct `Path` comparison is faster as it avoids allocations when the path is already UTF-8.
**Action:** Always hoist `format!` and other allocations out of loops. Prefer `Path` comparison over string conversion when dealing with file paths.

## 2025-05-15 - UTF-8 Correctness in String Capacity Calculation
**Learning:** Using `text.chars().count()` or iterating with `chars()` to calculate capacity for a `String` that will contain the same text (potentially with escapes) is both slow and incorrect for multi-byte UTF-8 characters. `String::with_capacity` expects bytes, not characters.
**Action:** Always use byte-based iteration (`as_bytes()`) or `len()` when calculating byte capacity for strings. For escaping, iterate over bytes and handle ASCII escape triggers, as they never appear as part of multi-byte UTF-8 sequences.

## 2025-05-15 - Fast-Path Buffer Scanning in Lexer
**Learning:** Lexer methods like `peek_char` and `next_char` often have overhead due to `Option` wrapping, state management (e.g., line splicing), and trigraph decoding. For common, non-special characters like whitespace, a tight loop scanning the raw buffer directly is significantly faster.
**Action:** Implement fast-path loops for common lexing tasks (like skipping whitespace or scanning simple identifiers) that operate directly on the byte buffer and break only when encountering special characters (`\`, `?`, `/`, etc.) or non-ASCII characters.

## 2026-05-20 - Redundant Filter-Collect in Parser Slices
**Learning:** Calling `.filter(...).cloned().collect()` on a token slice to remove delimiters (like `Eod`) is a significant performance bottleneck when the caller already guarantees the absence of those delimiters. This results in (N)$ redundant allocations and copies on every directive evaluation.
**Action:** Trust slice-based parsing boundaries. Avoid re-allocating token lists unless modification is strictly required.

## 2026-05-20 - Fast-Path Capacity Hinting from Raw Lengths
**Learning:** Calculating `String` capacity for cleaned token text (without line splices) can be done efficiently by using the raw `token.length` field as a safe upper bound. This avoids a redundant pass of expensive `get_text()` or `as_str()` calls which may involve hash lookups or enum matching.
**Action:** Use raw buffer lengths as capacity hints for string building in the preprocessor, then perform a single pass to populate with cleaned text.

## 2026-10-15 - Reducing Allocations in Macro Expansion
**Learning:** Macro expansion is a very hot path where every allocation counts. Returning `Vec<PPToken>` for every macro parameter replacement causes significant overhead. Using `Cow<'a, [PPToken]>` allows borrowing arguments directly from the input without allocation in the common case. Similarly, taking `Vec<T>` by value when the caller already has an owned vector avoids redundant `.to_vec()` clones.
**Action:** Favor `Cow` for return types of functions that might return either a borrow or a new collection. Transfer ownership of `Vec`s to avoid cloning when the caller doesn't need them anymore. Always use `Vec::with_capacity` when the minimum size is known (e.g., from the macro definition).

## 2024-05-22 - Optimizing Recursive Expansion and Token Stringification
**Learning:** Identifying macro recursion via string formatting and Path allocation in the preprocessor's main loop is a major bottleneck. Moving the check into expansion-specific paths and using direct string prefix/suffix matching on the existing Path object significantly reduces overhead. Additionally, tokens without an associated SourceId (built-ins) must be handled gracefully in buffer-based stringification.
**Action:** Favor direct string/path property checks over re-formatting existing information. Ensure buffer-based optimizations have safe fallbacks for tokens without backing source files.

## 2026-11-20 - Optimizing Macro Expansion and Virtual Buffer Creation
**Learning:** Macro expansion is a highly repetitive process where  is called for every expansion. Redundant passes over tokens (for length calculation, stringification, and metadata collection) and repeated HashMap/Path lookups for  checks are major bottlenecks.
**Action:** Use a single-pass approach to build the buffer and collect metadata simultaneously. Cache  results for expensive properties like  and use  for fast comparisons. Pre-allocate all buffers and vectors to avoid intermediate reallocations.

## 2026-11-20 - Optimizing Macro Expansion and Virtual Buffer Creation
**Learning:** Macro expansion is a highly repetitive process where `create_virtual_buffer_tokens` is called for every expansion. Redundant passes over tokens (for length calculation, stringification, and metadata collection) and repeated HashMap/Path lookups for `is_pasted` checks are major bottlenecks.
**Action:** Use a single-pass approach to build the buffer and collect metadata simultaneously. Cache `SourceId` results for expensive properties like `is_pasted` and use `Path::to_str()` for fast comparisons. Pre-allocate all buffers and vectors to avoid intermediate reallocations.

## 2026-11-25 - Reducing Allocations for HashMap Keys
**Learning:** Using `Vec<T>` as a key in a `HashMap` (or as part of a composite key) causes a heap allocation on every lookup, even for cache hits. This is especially costly in hot paths like type canonicalization.
**Action:** Use `SmallVec<[T; N]>` for collection fields in composite keys. This allows the key to be stack-allocated during lookup for the common case where the collection is small, significantly reducing heap pressure and improving cache locality.

## 2026-11-28 - Optimized MacroInfo with Arc for Token Lists
**Learning:** Cloning `MacroInfo` on every macro expansion and push/pop operation was a significant bottleneck due to `Vec<PPToken>` and `Vec<StringId>` causing repeated heap allocations and deep copies.
**Action:** Use `Arc<[T]>` for immutable collections in frequently cloned data structures like `MacroInfo`. This turns (N)$ clones into (1)$ reference count increments while maintaining read-only performance.
