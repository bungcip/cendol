## 2024-08-16 - Expensive Enum Cloning

**Learning:** Cloning heap-allocated data structures like `Box<Place>` and `Box<Operand>` in MIR enums (`src/mir.rs`) creates significant performance overhead due to repeated allocations, especially during semantic analysis.

**Action:** Replace `Box<T>` with `Rc<T>` for these recursive types. This makes cloning a cheap, atomic reference-counting operation, drastically reducing heap allocations when duplicating expression nodes.
