# Guardian - Semantic Constraints

- Ensure C11/C23 constraints are properly tested with negative tests.
- Verify completeness of types for operations like `sizeof`, `_Alignof`, pointer arithmetic, and `_Generic`.
- Qualifiers (`const`, `_Atomic`, `restrict`) have strict merging and compatibility rules.
- Bit-fields cannot be `_Atomic` or have a width exceeding their type.
- Control flow (`break`, `continue`, `case`, `default`) must be within appropriate enclosing statements.
