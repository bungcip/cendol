# Bolt - Performance Learnings

- Always prefer `rustc_hash::FxHashMap` over `hashbrown::HashMap` for performance.
- Use `smallvec::SmallVec` to avoid heap allocations on hot paths.
- Pre-allocate capacities for collections (`Vec::with_capacity`).
- Use `Arc<PathBuf>` for cached file paths instead of cloning `PathBuf`.
- Reuse allocations across function lowering (e.g. `clear()` instead of `new()`).
