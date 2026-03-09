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

2025-05-26 - [Structure and Union Member Constraints]

Learning: C11 6.7.2.1p3 requires that structure/union members must not have incomplete or function types (with the exception of FAM in structs). Incomplete type layout computation must be robust against recursion and errors to prevent "leaked" state in tracking sets like `layout_in_progress`, which could otherwise cause false "recursive type definition" errors for subsequent valid types. Mapping general layout errors (like `SizeOfIncompleteType`) to member-specific diagnostics (like `IncompleteType` or `MemberHasFunctionType`) with correct spans significantly improves compiler quality.
Action: Implement robust internal/external function splits for stateful semantic checks (like layout) and prioritize context-specific re-mapping of lower-level errors to provide precise diagnostics.

2025-05-27 - [Atomic Bit-fields Prohibition]

Learning: C11 6.7.2.4p4 explicitly prohibits bit-fields from having an atomic type, which is a subtle semantic constraint that is distinct from standard integer type checks. This constraint applies to both named and unnamed bit-fields. Prohibiting it during the lowering phase prevents potential backend failures or miscompilations when generating atomic instructions for non-byte-aligned memory locations.
Action: Always verify that qualifiers (especially _Atomic) are checked alongside base types when validating member-specific constraints like bit-fields.

2025-05-28 - [Integer Constant Expression Cast Restrictions]

Learning: C11 6.6p6 defines integer constant expressions very strictly: floating constants are ONLY allowed as the immediate operands of casts. This means `(int)1.0` is valid, but `(int)(1.0 + 1.0)` is not. Furthermore, constant evaluator `Cast` nodes must apply semantic truncation/masking according to the target type (e.g. `(char)257` is 1) as mandated by target layout.
Action: Enforce "immediacy" for floating constants in integer constant evaluation and ensure all casts in the constant evaluator perform proper integer range limiting based on the target type's layout.

2025-05-29 - [Enumeration Constant Range Constraints]

Learning: C11 6.7.2.2p2 requires that enumeration constants shall be representable as an 'int'. While many compilers allow larger values as an extension (supporting 'long' or 'unsigned long' underlying types for the enum itself), strict compliance requires diagnosing values outside the 'int' range. Implementing this as a warning preserves compatibility with existing extensions while meeting the C standard's requirement for a diagnostic on constraint violations.
Action: Enforce 'int' range checks for all enumeration constants during semantic lowering and ensure that both explicit values and implicit incremented values are validated.

2025-05-30 - [_Atomic Void Prohibition]

Learning: C11 _Atomic constraints (6.7.2.4p3 for specifiers and 6.7.3p5 for qualifiers) require that it only be applied to an object type that is not an array. While incomplete types (like 'struct S;') are object types, 'void' is explicitly NOT an object type per 6.2.5p1. Therefore, both _Atomic(void) and _Atomic void are constraint violations and must be rejected by the compiler.
Action: Enforce "object type" constraints by specifically rejecting the 'void' type in both qualifier merging and specifier resolution phases of semantic lowering.

2025-05-31 - [Ternary Operator Pointer Qualifier Merging]

Learning: C11 6.5.15p6 requires the result of a conditional operator with pointer operands to have a type that is a pointer to a qualified version of the type pointed to by either operand. Crucially, the qualifiers of the pointed-to type in the result must be the UNION of the qualifiers of the pointed-to types of both operands. Since 'TypeRegistry::composite_type' enforces qualifier identity for compatibility, the semantic analyzer must manually compute this qualifier union before constructing the result pointer type.
Action: When implementing language features that allow merging of differently qualified versions of compatible types (like ternary or certain assignments), explicitly compute the qualifier union for the resulting pointed-to types instead of relying on standard composite type helpers.

2025-06-01 - [Bit-field Declarator Recursion]

Learning: Bit-field widths in C can be part of complex declarators (e.g., `int *x : 1`). If the semantic analyzer only checks for `BitField` at the top level of a declarator, it will miss these cases, potentially silently accepting invalid types (like pointers or floats) that are prohibited for bit-fields by C11 6.7.2.1p5 and 6.7.2.4p4.
Action: Always use recursive extraction for declarator-specific attributes like bit-field widths to ensure they are consistently validated regardless of declarator complexity.

2025-06-02 - [Generic Selection Association Compatibility]

Learning: C11 6.5.1.1p2 prohibits any two associations in a `_Generic` selection from having compatible types (e.g., `int` vs `enum` with `int` base, or `int[10]` vs `int[]`). During semantic analysis, it is critical to visit the association nodes *before* performing compatibility checks, as types like `typeof(expr)` or complex declarators might not be fully resolved otherwise. Failing to do so can lead to false negatives where compatible types are silently accepted due to unresolved type information.
Action: Enforce phase ordering in `visit_generic_selection` where each association is visited to resolve types before it is checked for compatibility against previously seen associations and the controlling expression.

2025-06-03 - [Generic Selection Qualifier Distinctness]

Learning: C11 6.5.1.1p2 mandates that generic association type names specify complete object types and that no two associations specify compatible types. Crucially, 'int' and 'const int' are NOT compatible types. While the controlling expression undergoes lvalue conversion (stripping top-level qualifiers), the associations maintain their qualifiers for type matching. A compiler must correctly distinguish these qualified types as non-compatible to allow them as distinct associations, while still rejecting truly compatible duplicates.
Action: Implement regression tests that verify the distinction between qualified and unqualified types in generic associations to prevent incorrect duplicate detection or matching.

2025-06-04 - [Type Alias Consistency in Semantic Checks]

Learning: Semantic properties like completeness (`is_complete`) and variably-modified status (`is_variably_modified`) must be checked against the *resolved* type, not just the initial type reference. When using constructs like `typeof(expr)`, the compiler produces a `TypeKind::Alias`. If the property check doesn't use a resolution helper (like `TypeRegistry::get`), it will incorrectly treat the alias as its own base type (often a builtin or simple type), potentially bypassing C11 constraints (e.g., 6.5.1.1p2 requiring complete object types in `_Generic` associations). Unifying these checks to use the registry's resolution logic ensures consistency across all type representations, including inline pointers/arrays and aliases.
Action: Always use `TypeRegistry::get(ty)` or similar resolution helpers when checking semantic properties of a `TypeRef` to ensure aliases and inline types are correctly handled.

2025-06-05 - [sizeof and _Alignof Semantic Constraints]

Learning: C11 6.5.3.4p1 explicitly prohibits `sizeof` and `_Alignof` on function types and incomplete types (including `void`), and `sizeof` on bit-fields. While function-to-pointer decay typically happens in expressions, it is suppressed inside `sizeof` (6.3.2.1p3), meaning the operator correctly sees the function type and must trigger a constraint violation. Similarly, `_Alignof` requires a complete object type, distinguishing it from `sizeof` which can sometimes handle VLAs (though Cendol currently marks VLA sizeof as an unsupported feature).
Action: Always verify that operators which suppress standard conversions (like `sizeof`, `_Alignof`, and `&`) are tested against the original types they receive, especially for types that are normally transformed (like functions or arrays).

2025-06-06 - [Compound Literal Semantic Constraints]

Learning: C11 6.5.2.5p1 imposes strict constraints on compound literals: they must specify a complete object type or an array of unknown size (which is then completed), and they specifically prohibit variably modified types (VLAs) and function types. Enforcing these early in semantic analysis prevents layout computation failures and backend miscompilations for types that lack a fixed static size or represent non-object entities.
Action: Centralize compound literal type validation in the semantic analyzer, ensuring that the exception for incomplete arrays is strictly limited to those that can be completed by the following initializer.

2025-06-07 - [Generic Selection LValue Property Propagation]

Learning: C11 6.5.1.1p5 requires the result of a `_Generic` selection to have the type and value category of its selected association. Crucially, if the selected expression is a bit-field or has the `register` storage class, these properties must be propagated to the `_Generic` expression itself so that operators like `&` and `sizeof` can correctly enforce their respective constraints (e.g., 6.5.3.2p1 prohibiting `&` on bit-fields and register variables).
Action: Ensure that semantic property queries (like `is_lvalue`, `get_bitfield_width`, and `is_register_variable`) recursively inspect the selected association of `_Generic` nodes to maintain semantic correctness across expression boundaries.
