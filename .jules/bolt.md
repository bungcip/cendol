## 2024-07-25 - Two-Pass Allocation for Sequential Items
**Learning:** A common performance anti-pattern in this codebase is processing a peekable iterator in a single pass, where an intermediate collection (like a `String` or `Vec`) is built up, leading to multiple costly reallocations.
**Action:** For future optimizations involving sequential item processing, I will favor a two-pass approach. First, iterate (or peek ahead) to calculate the final required capacity. Second, perform a single allocation with `with_capacity`. Third, iterate again to populate the collection. This avoids N reallocations, providing a significant performance improvement.

## 2026-01-31 - Path Comparison and Loop Invariant Hoisting
**Learning:** Calling `format!` and `to_string_lossy()` inside a hot loop (like `is_recursive_expansion`) is a major performance bottleneck due to repeated heap allocations. Direct `Path` comparison is faster as it avoids allocations when the path is already UTF-8.
**Action:** Always hoist `format!` and other allocations out of loops. Prefer `Path` comparison over string conversion when dealing with file paths.
