## 2024-05-19 - SemanticError::ZeroOrNegativeSizeArray Test Coverage

**Learning:** Adding test coverage for `SemanticError::ZeroOrNegativeSizeArray` on C23 arrays with no elements (e.g. `int arr[] = {};`) hit the targeted code path accurately (`src/semantic/lowering.rs`). Ensuring tests pass correctly using `cargo test -p cendol` verified regressions. It's helpful to remember that `-std=c23` must be enabled to trigger this semantic error constraint.
**Action:** Successfully increased test coverage on C23 empty array behaviors in the compiler without redundant refactoring.

## 2024-11-23 - Memoized Header Resolution Cache

**Learning:** During C compilation/preprocessing, header path resolution is repeatedly queried (e.g. via `#include` directive lookups) resulting in numerous redundant filesystem `exists` (system call) checks, even for files that are already loaded/cached in the compiler. Applying interior-mutable memoization caches (`RefCell<FxHashMap<...>>`) to `HeaderSearch` dramatically avoids these disk I/O operations and speeds up compiling/parsing of large files like SQLite by ~6%.
**Action:** Always consider memoizing filesystem resolution paths and caching directory existence lookups for compilers/preprocessors where static file trees are read repeatedly.
