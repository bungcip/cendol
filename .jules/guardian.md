2025-01-24 - Function Return Type Qualifier Preservation

Learning: C11 §6.7.6.3p15 requires compatible return types for function compatibility. Cendol was dropping return type qualifiers during lowering by using `TypeRef` instead of `QualType` in `TypeKind::Function`. This caused `_Generic` to incorrectly match distinct function pointers (e.g., `int (*)(void)` vs `const int (*)(void)`) as duplicates and allowed unsafe assignments.
Action: Upgraded `TypeKind::Function` to use `QualType` for its return type and ensured all semantic checks (compatibility, composition, assignment) respect return qualifiers while maintaining parameter qualifier stripping for compatibility.
