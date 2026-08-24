# Guardian - Semantic Constraints

- Ensure C11/C23 constraints are properly tested with negative tests.
- Verify completeness of types for operations like `sizeof`, `_Alignof`, pointer arithmetic, and `_Generic`.
- Qualifiers (`const`, `_Atomic`, `restrict`) have strict merging and compatibility rules.
- Bit-fields cannot be `_Atomic` or have a width exceeding their type.
- Control flow (`break`, `continue`, `case`, `default`) must be within appropriate enclosing statements.
2025-01-28 - [Extern with Initializer vs Scope Constraints]

Learning: According to C11 6.7.9p5, an `extern` declaration with an initializer is an error if it occurs at block scope (it emits "invalid initializer"). However, at file scope, an `extern` declaration with an initializer is treated as a definition and is completely valid C code (though it may trigger warnings for other reasons).

Action: Tests for `extern` initializers must explicitly test both block scope (where it should fail) and file scope (where it should succeed) to ensure correct semantic phase behavior and adherence to the C11 specification.
2025-01-28 - [Restrict Qualifier Validation Constraints]

Learning: According to C11, the `restrict` qualifier is only valid when applied to pointer types (excluding function pointers). Validating this during `CompilePhase::SemanticLowering` ensures correct semantic boundaries without polluting parser syntax paths.

Action: Ensure tests that check invalid type qualifiers (like `restrict` on a non-pointer) apply the qualifier properly and cover a broad range of non-pointers including standard primitives, function pointers, and arrays (via typedefs).
