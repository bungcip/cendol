This file is for Guardian's critical, non-routine learnings about the Cendol compiler.

2025-05-14 - [Generic Selection Constraints]

Learning: C11 `_Generic` constraints (6.5.1.1) require both that the controlling expression matches at most one association AND that no two associations specify compatible types. Compatibility checking for `_Generic` must strip qualifiers from both the associations and the decayed controlling expression.
Action: Always verify that constraints involving type compatibility (like `_Generic` or `typedef` redefinition) correctly handle qualifiers and decay according to the specific rules of that language feature.

2025-05-15 - [Completeness in Generic Selection]

Learning: Beyond compatibility, `_Generic` selection (C11 6.5.1.1p2) strictly requires controlling expressions and associations to be complete object types. While arrays decay to complete pointers, `void` and incomplete `struct`s remain incomplete and must trigger semantic errors.
Action: Explicitly check for type completeness in language features that require object types to be complete for layout or selection purposes.

2025-05-16 - [Function Scope and Linkage Invariants]

Learning: C11 scope rules (6.2.1p4) require function parameters and the outermost block of the function body to share the same scope. Treating them as separate scopes allows illegal redefinitions (C11 6.7p3). Additionally, linkage inheritance for functions (6.2.2p5) allows 'extern' to follow 'static' but not vice-versa.
Action: Always ensure that scope boundaries correctly match language semantics, especially when multiple grammatical constructs (like parameter lists and compound statements) logically belong to the same scope.

2025-05-17 - [Composite Types and Redeclarations]

Learning: C11 composite type rules (6.2.7p3) require that all declarations of the same identifier in a translation unit refer to a single composite type. Simply checking for type compatibility on redeclaration is insufficient; the compiler must compute the composite type (e.g., merging an incomplete array with a complete one) and update the symbol table entry so that subsequent uses (like 'sizeof') reflect the most complete type information.
Action: Implement and use a 'composite_type' mechanism during redeclaration checks to ensure symbol types are correctly refined across multiple declarations.

2025-05-18 - [_Alignas Constraints and Strictness]

Learning: C11  (6.7.5) has strict constraints on where it can appear: it is prohibited in s, function declarations, function parameters, and  objects. Additionally, it cannot specify an alignment less strict than the type's natural alignment. While  is valid and has no effect, any other value must be a power of two and satisfy the strictness constraint.
Action: Implement and enforce alignment constraints during the semantic lowering phase to ensure C11 compliance and prevent invalid object layouts.

2025-05-18 - [_Alignas Constraints and Strictness]

Learning: C11 `_Alignas` (6.7.5) has strict constraints on where it can appear: it is prohibited in `typedef`s, function declarations, function parameters, and `register` objects. Additionally, it cannot specify an alignment less strict than the type's natural alignment. While `_Alignas(0)` is valid and has no effect, any other value must be a power of two and satisfy the strictness constraint.
Action: Implement and enforce alignment constraints during the semantic lowering phase to ensure C11 compliance and prevent invalid object layouts.
