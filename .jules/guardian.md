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

Learning: C11 `_Alignas` (6.7.5) has strict constraints on where it can appear: it is prohibited in `typedef`s, function declarations, function parameters, and `register` objects. Additionally, it cannot specify an alignment less strict than the type's natural alignment. While `_Alignas(0)` is valid and has no effect, any other value must be a power of two and satisfy the strictness constraint.
Action: Implement and enforce alignment constraints during the semantic lowering phase to ensure C11 compliance and prevent invalid object layouts.

2025-05-19 - [_Atomic Constraints and Specifiers]

Learning: C11 (6.7.2.4 and 6.7.3) enforces strict constraints on _Atomic. The qualifier is prohibited on array and function types. The _Atomic(type-name) specifier is even stricter: it also prohibits already atomic types and qualified types, and it requires the type-name to designate an object type. Redundant _Atomic qualifiers in a specifier-qualifier list are allowed and collapsed, but nested _Atomic specifiers are specifically prohibited by the specifier's constraints.
Action: Enforce _Atomic constraints during semantic lowering in both qualifier merging and type-name resolution. Ensure that _Atomic(type-name) correctly results in an atomic-qualified version of the inner type.

2025-05-20 - [Restrict Qualifier Constraints]

Learning: C11 `restrict` constraints (6.7.3p2) require that it shall be a pointer type AND the pointed-to type shall be an object type or incomplete type. A function type is NOT an object type or an incomplete type. Therefore, `void (* restrict f)(void);` is invalid and must be rejected during semantic analysis.
Action: Enforce pointed-to type constraints for the `restrict` qualifier in `merge_qualifiers_with_check` by ensuring the target type is not a function type.

2025-05-21 - [Function Parameter Storage Class Constraints]

Learning: C11 (6.7.6.3p2) restricts the storage-class specifiers in a function parameter declaration to ONLY `register`. Specifiers like `static`, `extern`, `auto`, `typedef`, or `_Thread_local` are illegal. Furthermore, while `register` is allowed, its semantics must be correctly propagated to the function's scope to ensure that operations like taking the address of the parameter are properly rejected.
Action: Enforce parameter storage class constraints during semantic lowering and ensure the storage class is preserved in the symbol table for subsequent semantic analysis (e.g., lvalue address-of checks).

2025-05-22 - [Incomplete Type Constraints for Linkage and Parameters]

Learning: C11 enforces strict completeness rules for object declarations depending on linkage. Identifiers with no linkage (block scope, non-extern) must be complete (6.7p7). Tentative definitions with internal linkage (file scope, static) must also be complete (6.9.2p3). However, tentative definitions with external linkage (file scope, non-static) can be incomplete as they are completed at the end of the TU. Function parameters in definitions must be complete after adjustment (6.7.6.3p4), meaning 'void f(int arr[])' is OK as it decays to a complete pointer, but 'void f(void x)' is not.
Action: Enforce completeness checks in 'visit_variable_decl' and 'visit_function_parameters' by carefully distinguishing linkage and storage classes. Ensure initializers have a chance to complete array types before the check occurs.

2025-05-23 - [Typedef Redefinition and Type Identity]

Learning: C11 6.7p3 requires that a typedef redefinition in the same scope denote the SAME type. This is stricter than type compatibility. For example, 'int[]' and 'int[10]' are compatible but not the same type, and thus a typedef redefinition from one to the other must be rejected. However, differences that do not affect type identity (like function parameter names) are ignored due to canonicalization.
Action: Use strict QualType equality (which relies on canonical TypeRefs and qualifier masks) for typedef redefinition checks instead of 'is_compatible'.

2025-05-24 - [Function Specifier Constraints]

Learning: C11 6.7.4p1 requires that function specifiers ('inline' and '_Noreturn') only be used in the declaration of an identifier that is a function. This means they must be rejected for typedefs, struct/union members, and tag declarations (forward decls or definitions), even if the underlying type is a function pointer.
Action: Centralize function specifier validation in semantic lowering to ensure all non-function declaration paths (variables, typedefs, members, tags) correctly enforce these constraints.

2025-05-25 - [_Noreturn Fall-through and Loop Breaks]

Learning: `can_fall_through` analysis for `_Noreturn` compliance must distinguish between truly infinite loops and those that can exit via `break`. A loop without a condition (like `for(;;)`) or with a constant true condition (like `while(1)`) only satisfies `_Noreturn` if it contains no `break` statements targeting it. Shallow scanning for `NodeKind::Break` (avoiding nested loops) combined with `const_eval` for loop conditions provides a robust safeguard against miscompilation of divergent control flow.
Action: Always combine condition analysis with internal control-flow jump detection (like `break`) when validating divergent or non-returning constructs.
