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
