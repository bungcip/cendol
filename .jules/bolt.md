## 2024-05-19 - SemanticError::ZeroOrNegativeSizeArray Test Coverage

**Learning:** Adding test coverage for `SemanticError::ZeroOrNegativeSizeArray` on C23 arrays with no elements (e.g. `int arr[] = {};`) hit the targeted code path accurately (`src/semantic/lowering.rs`). Ensuring tests pass correctly using `cargo test -p cendol` verified regressions. It's helpful to remember that `-std=c23` must be enabled to trigger this semantic error constraint.
**Action:** Successfully increased test coverage on C23 empty array behaviors in the compiler without redundant refactoring.
