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

Learning: C11 6.5.3.4p1 explicitly prohibits `sizeof` and `_Alignof` on function types and incomplete types (including `void`), and `sizeof` on bit-fields. While function-to-pointer decay typically happens in expressions, it is suppressed inside `sizeof` (6.3.2.1p3), meaning the operator correctly sees the function type and must trigger a constraint violation. Similarly, `_Alignof` requires a complete object type, distinguishing it from `sizeof` which correctly handles VLAs at runtime.
Action: Always verify that operators which suppress standard conversions (like `sizeof`, `_Alignof`, and `&`) are tested against the original types they receive, especially for types that are normally transformed (like functions or arrays).

2025-06-06 - [Compound Literal Semantic Constraints]

Learning: C11 6.5.2.5p1 imposes strict constraints on compound literals: they must specify a complete object type or an array of unknown size (which is then completed), and they specifically prohibit variably modified types (VLAs) and function types. Enforcing these early in semantic analysis prevents layout computation failures and backend miscompilations for types that lack a fixed static size or represent non-object entities.
Action: Centralize compound literal type validation in the semantic analyzer, ensuring that the exception for incomplete arrays is strictly limited to those that can be completed by the following initializer.

2025-06-07 - [Generic Selection LValue Property Propagation]

Learning: C11 6.5.1.1p5 requires the result of a `_Generic` selection to have the type and value category of its selected association. Crucially, if the selected expression is a bit-field or has the `register` storage class, these properties must be propagated to the `_Generic` expression itself so that operators like `&` and `sizeof` can correctly enforce their respective constraints (e.g., 6.5.3.2p1 prohibiting `&` on bit-fields and register variables).
Action: Ensure that semantic property queries (like `is_lvalue`, `get_bitfield_width`, and `is_register_variable`) recursively inspect the selected association of `_Generic` nodes to maintain semantic correctness across expression boundaries.

2025-06-08 - [Pointer Arithmetic Completeness Constraints]

Learning: C11 6.5.6p2 and 6.5.6p3 impose strict requirements on pointer arithmetic: operands must be pointers to complete object types. This means addition and subtraction are prohibited for pointers to 'void' (which is incomplete), pointers to incomplete structures/unions, and pointers to functions (which are not object types). Simply checking for 'void*' is insufficient as it misses other incomplete types and function pointers, potentially leading to invalid code generation or backend failures.
Action: Enforce complete object type constraints for all pointer arithmetic operations in the semantic analyzer and verify with negative tests covering diverse incomplete and non-object types.

2025-06-09 - [Relational Pointer Constraints and Function Pointers]

Learning: C11 6.5.8p2 restricts relational operators (<, <=, >, >=) to pointers to compatible object types or compatible incomplete types. Since function types are neither object types nor incomplete types (per 6.2.5), relational comparisons between function pointers are constraint violations. This distinguishes them from equality operators (==, !=), which explicitly allow function pointer comparisons (6.5.9p2).
Action: Enforce complete/incomplete object type constraints for relational operators while maintaining broader compatibility for equality operators to ensure standard compliance.

2026-03-15 - [Increment and Decrement Completeness Constraints]

Learning: C11 6.5.3.1 (prefix) and 6.5.2.4 (postfix) require that the operand of an increment or decrement operator have a scalar type. Furthermore, because these operators are defined in terms of addition/subtraction of 1 (6.5.6), they inherit the constraint that pointer operands must point to complete object types. This prohibits `++` and `--` on `void*`, incomplete structures, and function pointers, even if the operand is an lvalue.
Action: Centralize increment/decrement operand validation in a helper that checks for both scalarity and pointer-to-complete-object-type constraints to ensure consistent enforcement across prefix and postfix variants.

2026-03-16 - [Subscript Operator Completeness Constraints]

Learning: C11 6.5.2.1p1 requires one subscript operand to be a pointer to a complete object type and the other to be an integer. This prohibits subscripting `void*`, function pointers, and pointers to incomplete types. Crucially, incomplete arrays (e.g. 'extern int a[];') are PERMITTED because they decay to a pointer to a complete object type ('int*'), distinguishing them from arrays of incomplete types which are inherently illegal.
Action: Enforce complete object type and integer constraints in 'visit_index_access', ensuring that both pointer-based and array-based bases are validated for element completeness.

2026-03-17 - [_Generic Controlling Expression Completeness]

Learning: C11 6.5.1.1p2 mandates that the controlling expression of a `_Generic` selection shall be an expression of a complete object type or the `void` type. Because function types are not object types and incomplete arrays/structures are not complete, they must be rejected. Performing this check on the decayed type is incorrect, as decay transforms functions and arrays into complete pointer types, potentially bypassing the constraint.
Action: Enforce completeness and object type constraints on the original (undecayed) type of the controlling expression in `_Generic` selection, while maintaining the explicit exception for the `void` type.

2026-03-18 - [Function Parameter Completeness Constraints]

Learning: C11 6.7.6.3p4 and 6.7.6.3p10 require that all function parameters have complete object type (after adjustment), regardless of whether the declaration is a definition. The only exception is a single unnamed parameter of type 'void'. Enforcing this check only during function definitions allows invalid types (like named 'void' or incomplete structs) to bypass semantic validation in prototypes, potentially leading to issues in later phases or non-compliant behavior.
Action: Enforce parameter completeness in 'visit_function_parameters' for all function declarators, while carefully preserving the special case for unnamed '(void)' parameter lists.

2026-03-19 - [Selection Expression Property Propagation]

Learning: C11 (via DR 481) requires that selection expressions (`_Generic` and `__builtin_choose_expr`) act as transparent wrappers for the semantic properties of their selected associations. This includes lvalue-ness, bit-field status, `register` storage class, and null-pointer-constant (NPC) status. Failure to propagate these properties leads to constraint bypasses (e.g., taking the address of a bit-field wrapped in `_Generic`) or incorrect type mismatches (e.g., rejecting an NPC wrapped in `__builtin_choose_expr` where a pointer is expected).
Action: Ensure all expression property queries (like `is_lvalue`, `is_register_variable`, `get_bitfield_width`, and `is_null_pointer_constant`) recursively inspect the selected branch of selection expressions.

2026-03-20 - [Member Completeness and Span Propagation]

Learning: C11 6.7.2.1p3 constraints on structure members (prohibiting incomplete or function types) are best enforced during semantic lowering when the record is being completed. However, because record completion often triggers layout computation, errors like 'SizeOfIncompleteType' or 'RecursiveType' can originate deep in the type registry. Ensuring these are caught during lowering and associated with the correct member span is critical for diagnostic quality. Testing this at the `SemanticLowering` phase rather than later (like MIR) ensures that invalid types are rejected as soon as they are defined.
Action: Always verify that structural constraints (like member types) are enforced during the lowering/definition phase and that diagnostics point to the relevant declaration rather than just the start of the containing block.

2026-03-21 - [Function Type Members via Typedef]

Learning: C11 6.7.2.1p3 prohibits structure/union members from having a function type. While direct function declarations in structs are easily caught, function types introduced via 'typedef' must also be rejected. In Cendol, this validation occurs during the record completion and layout computation phase in 'TypeRegistry'. This ensures that even types hidden behind multiple layers of aliases are correctly validated for completeness and object-type status before they are used in memory layout or code generation.
Action: Always include tests for constraint enforcement that use 'typedef' to ensure that semantic checks are performed on the underlying resolved types rather than just the syntactic representation.

2026-03-22 - [_Alignof on Bit-fields Constraint]

Learning: While C11 only defines '_Alignof' for type names (6.5.3.4p2), common extensions (GCC/Clang) allow it for expressions. Because bit-fields do not have a byte-aligned address and their layout is implementation-defined, applying '_Alignof' to a bit-field must be rejected, mirroring the constraint for 'sizeof'. Centralizing these checks in 'visit_sizeof_alignof' ensures consistent enforcement across both operators.
Action: When supporting language extensions that mirror standard operators (like '_Alignof' mirroring 'sizeof'), always ensure that base-language constraints (like bit-field prohibitions) are also mirrored and correctly diagnosed.

2026-03-25 - [Explicit Cast Constraints and Identity Casts]

Learning: C11 6.5.4p2 mandates that both the target type (if not 'void') and the operand of an explicit cast must have scalar types. This prohibits casting between structures/unions and integers or other non-scalar types. However, common real-world code and existing test suites (like Cendol's codegen tests) often rely on 'identity casts'—casting a structure to its own type (or a compatible one). While strictly a constraint violation in C11, permitting these identity casts as a compiler extension maintains compatibility with standard practice while still rejecting truly invalid non-scalar conversions.
Action: Enforce scalar constraints for explicit casts in 'visit_expression_node' but implement an explicit exception for identity casts of compatible types to balance standard compliance with practical compatibility.

2026-03-24 - [VLA Star Scope Constraints]

Learning: C11 6.7.6.2p4 restricts the use of `[*]` array size to function prototype scope only. This means it is invalid in file scope, block scope (outside of parameter lists), and even in function definitions (where parameters have block scope). Cendol previously lacked this constraint, potentially allowing invalid VLAs to reach the backend.
Action: Implemented scope-aware tracking in `LowerCtx` to distinguish between prototype scope and definition/block scope, and added a specific diagnostic for illegal `[*]` usage.

2026-03-23 - [VLA Size Expression Validation]

Learning: C11 6.7.6.2p1 requires that variable array size expressions have an integer type. In Cendol, these expressions are resolved during semantic analysis via `visit_type_exprs`. Simply visiting the expression node is insufficient; the compiler must also verify the resulting type of the size expression. This is critical because VLA sizes can appear within complex types (e.g. `int (*p)[n]`) that might be processed without a direct variable declaration context.
Action: Always enforce type constraints on expressions embedded within types (like VLA sizes or `typeof`) during the recursive type traversal phase of semantic analysis.

2026-03-25 - [_Generic Qualifier Matching and Lvalue Conversion]

Learning: C11 6.5.1.1p2 requires that the type of the controlling expression in a `_Generic` selection be compared after lvalue conversion. This means that if the controlling expression is an lvalue with a qualified type (e.g., `const int`), the type used for matching is the unqualified version (`int`). However, pointer-to-qualified types (e.g., `const int *`) are only stripped of their top-level qualifiers (like `const` in `const int * const`), preserving the qualification of the pointed-to type.
Action: When testing or implementing `_Generic` selection, ensure that the lvalue conversion rules are correctly applied to the controlling expression's type before matching against associations, while keeping association types themselves fully qualified.

2026-03-25 - [_Alignas on Variably Modified Types]

Learning: C11 6.7.5p2 explicitly prohibits alignment specifiers (_Alignas) on objects with variably modified types. This includes not only Variable Length Arrays (VLAs) but also any type derived from them, such as pointers to VLAs. Enforcing this during semantic lowering prevents potential backend issues when attempting to align objects whose size is only known at runtime.
Action: Always verify that constraints on specifiers (like _Alignas) are checked against the full variably-modified status of the type, especially when extensions or standard features (like VLAs) are involved.

2026-03-26 - [Variably Modified Structure Members Constraint]

Learning: C11 6.7.2.1p9 prohibits structure and union members from having a variably modified (VM) type. While direct VLAs were already rejected, pointers to VLAs or multi-dimensional arrays with variable dimensions are also VM types and must be prohibited. Importantly, Flexible Array Members (FAMs) are incomplete arrays and thus technically not 'complete object types', but they are NOT variably modified unless their element type is VM. Centralizing this check in 'TypeRegistry::compute_record_layout' using 'is_variably_modified' ensures that all nested VM types are caught, including VM FAMs like 'int a[][n]', while still permitting standard FAMs like 'int a[]'.
Action: Always use the recursive 'is_variably_modified' check rather than simple type matching when enforcing C11 constraints on 'objects' or 'members', as VM status can be hidden behind pointers, arrays, or typedefs.

2026-04-04 - [Flexible Array Member Nesting in Unions]

Learning: C11 6.7.2.1p18 constraints on Flexible Array Members (FAM) have subtle interactions with unions. While a structure with a FAM is a complete type and thus can validly be a member of a union, the resulting union "contains" a FAM recursively. This makes the union type subject to the same nesting constraints as FAM-structures (e.g., it cannot be an array element or a non-last member of another structure). Robust enforcement requires recursive property detection in the type registry and context-aware validation in the semantic lowerer to distinguish between 'allowing' a FAM in a union and 'propagating' its presence for further checks.
Action: Implement recursive property checks for 'has_flexible_array_member' in the type registry and ensure semantic validation passes correct context (like 'is_union') to avoid false positives during member definition while maintaining strict correctness for nested usage.

2026-04-10 - [_Generic Multiple Match Constraint]

Learning: C11 6.5.1.1p2 mandates that the controlling expression of a `_Generic` selection shall be compatible with at most one generic association. Picking only the first match is insufficient as it silently accepts ambiguous code. Furthermore, associations like `int(*)[10]` and `int(*)[20]` are NOT compatible with each other, but both can be compatible with a controlling expression of type `int(*)[]` (pointer to incomplete array).
Action: Ensure that `_Generic` selection continues checking all associations even after a match is found, to detect and report ambiguity errors when multiple associations are compatible with the controlling expression.

2026-04-11 - [Block-Scope Function Declarations and Lazy MIR Lowering]

Learning: C11 prohibits 'static' storage class for function declarations in block scope. Furthermore, 'extern' function declarations in block scope can be missed by a global 'pre-declare' pass that only scans top-level symbols. If these block-scope declarations are referenced, the MIR generator must handle them lazily by declaring the function on-the-fly using symbol table metadata, otherwise it may encounter unexpected 'None' values when resolving identifiers to function addresses.
Action: Enforce storage class constraints for block-scope functions in semantic lowering and implement lazy, metadata-driven function declaration in the MIR generator to ensure robust handling of all valid C scope-linkage combinations.

2026-04-15 - [Modifiable LValue Completeness Constraint]

Learning: C11 6.3.2.1p1 requires the left operand of an assignment to be a modifiable lvalue, which specifically prohibits objects with incomplete types. While incomplete arrays decay to pointers (making them complete), other incomplete types like 'void' (via dereference) or forward-declared structures remain incomplete and must be rejected during semantic analysis of assignments.
Action: Enforce completeness checks in 'check_lvalue_and_modifiable' for all lvalues to ensure standard compliance for assignments and other mutating operations.

2026-04-16 - [Variably Modified Type Linkage and Storage Constraints]

Learning: C11 6.7.6.2p2 mandates that objects with variably modified (VM) types must have no linkage and must not have static or thread storage duration. This applies to all VM types, including pointers to VLAs, not just direct VLAs. File-scope declarations (regardless of 'static') and block-scope 'extern' or 'static'/'_Thread_local' declarations of VM types are constraint violations.
Action: Always use `TypeRegistry::is_variably_modified` to enforce storage and linkage constraints on declarations, and distinguish between linkage and storage duration when reporting diagnostics for these violations.
2026-04-20 - [Function Parameter Compatibility and _Atomic Qualifiers]

Learning: C11 §6.7.6.3p15 mandates that top-level qualifiers (const, volatile, restrict) on function parameters be ignored when determining type compatibility. However, this rule does NOT apply to the _Atomic qualifier, as an atomic-qualified type is fundamentally incompatible with its non-atomic counterpart according to §6.2.5p29. Furthermore, this compatibility check must happen AFTER array-to-pointer and function-to-pointer adjustment (§6.7.6.3p7-8). For example, 'void f(int a[const])' is compatible with 'void f(int *a)', but 'void f(_Atomic int a)' is NOT compatible with 'void f(int a)'.
Action: Implemented 'QualType::strip_for_parameter' to specifically handle these C11 qualifier rules and updated 'TypeRegistry::is_compatible' and 'composite_type' to ensure correct function type matching and merging, particularly for _Generic selection.

2026-04-25 - [Enum Compatibility and Transitivity in _Generic]

Learning: C11 (and practical compiler implementation) requires that enum compatibility be handled carefully, especially regarding transitivity. While each enumerated type is compatible with an integer type, different enum types are NOT compatible with each other, even if they have the same size and underlying type. If a compiler incorrectly treats them as compatible (e.g., by only checking their size and integer-ness), it violates the non-transitivity of compatibility and causes incorrect behavior in `_Generic` selection, where multiple distinct enum associations might be wrongly rejected as duplicate compatible types.
Action: Explicitly distinguish between different enum types during compatibility checks, ensuring that enum-to-integer compatibility does not lead to enum-to-enum compatibility.

2026-05-15 - [_Generic Association VM Type Constraint]

Learning: C11 6.5.1.1p2 prohibits variably modified (VM) types in generic associations. This constraint applies not only to direct VLAs (e.g. 'int[n]') but also to any VM type, including pointers to VLAs (e.g. 'int(*)[n]'). While Cendol's 'is_variably_modified' correctly handles this recursion, explicit tests are required to ensure these cases are consistently rejected with 'SemanticError::GenericVlaAssociation' to prevent them from reaching later compiler phases.
Action: Always test VM type constraints using both direct VLAs and derived VM types (like pointers or multi-dimensional arrays) to ensure complete coverage of the language's VM type classification.

2026-05-16 - [Typedef Redefinition Type Identity vs Compatibility]

Learning: C11 6.7p3 requires that typedef redefinitions in the same scope denote the exact SAME type, not merely compatible types. This is a subtle distinction. While `int[]` and `int[10]` are compatible, they are not the same type. Similarly, `int` and `const int` are compatible in some contexts, but not the same. Enforcing strict type identity using `aliased_type != final_ty` during lowering prevents invalid redefinitions that would otherwise pass simple compatibility checks.
Action: Add dedicated regression tests for `typedef` redefinition specifically targeting cases where types are compatible but not identical, to prevent regressions in this strict type identity constraint.

2024-05-20 - [Modifiable Lvalue: Const qualification propagation]

Learning: [C11 6.5.16p2 requires the left operand of an assignment to be a modifiable lvalue. Structs containing `const` qualified members are not modifiable lvalues, and any assignment to such structs must be rejected. The type system correctly identifies `const` qualification recursively for structs, and this applies not just to simple assignment but also increment/decrement and compound assignments. Tests added to enforce rejecting assignments/increments to const-containing structs and incomplete types to prevent compiler crashes or invalid codegen.] Action: [Always include tests for aggregate assignments when adding new type qualifiers or modifying lvalue checking logic.]
2024-05-18 - [Function Return Type Constraints]

Learning: C11 6.7.6.3p1 states that functions cannot return arrays or function types. However, when parsing code, `int f()[10];` or `int f()();` are often rejected as invalid syntax during the parsing phase ("Declaration not allowed in this context"). To properly test the semantic analysis phase enforcement of this constraint without parser interference, one must use `typedef` to obscure the array or function type, e.g., `typedef int arr[10]; arr f();`.
Action: When testing semantic constraints involving complex derived types (like arrays or functions) in positions that might have syntactic limitations, use `typedef`s to bypass parser rejections and ensure the semantic rules are correctly enforced.

2024-05-25 - [Block-scope Thread-Local Validation]

Learning: C11 §6.7.1p3 requires that `_Thread_local` variables in block scope must also be specified with either `static` or `extern` storage-class specifiers. Without explicitly testing this invariant, the compiler could easily accept automatic `_Thread_local` variables, breaking compilation or runtime assumptions as thread-local semantics do not apply to automatic storage. Action: Ensure storage class modifier combinations are robustly checked, especially for nested scopes and specific thread-local semantics.

2024-05-31 - [Nested Pointer Qualifiers]

Learning: C11 6.5.16.1p1 requires that operands for assignment are pointers to qualified or unqualified versions of compatible types. For nested pointers, `int **` and `const int **` are NOT compatible types. The compiler correctly prevents implicit conversion for these assignments and returns a type mismatch rather than just emitting a "discards qualifiers" warning. We need to test to ensure we don't accidentally enable this type conversion implicitly because the outer qualifiers would silently be added, which breaks C11 safety assumptions around pointer aliasing. Action: Add tests specifically verifying that type conversions fail outright for incompatible nested pointers like `int **` assigned to `const int **`.
2024-10-31 - [Switch Multiple Default Labels]

Learning: A `switch` statement can correctly contain zero or one `default` label. However, the parser and semantic analyzer must properly isolate `default` label checks to the innermost enclosing `switch`. The `switch_stack` needs to track `default_seen` correctly for nested switches without bleeding the state outward or inward across boundaries.
Action: Add tests using `run_fail_with_diagnostic` targeting `CompilePhase::Mir` (since the lowering validates switch structure) to ensure a single `switch` rejects multiple `default` labels while properly allowing a nested `switch` to also define its own `default` label. Ensure the precise span (line, column) of the secondary `default` label is validated.

2024-06-05 - [Parameter Storage Class Constraints]

Learning: C11 §6.7.6.3p2 specifies that the only storage-class specifier that shall occur in a parameter declaration is `register`. The compiler correctly enforced this in lowering via `SemanticError::InvalidStorageClassForParameter`, but lacked dedicated integration tests to verify this exact rejection for `static`, `extern`, and `auto`. We implemented a dedicated test file to guarantee this semantic rule is always enforced properly.
Action: Implement specific targeted tests for all invalid combinations of parameter storage classes to ensure regressions don't occur when refactoring the semantic analyzer or function parameter parsing logic.

2025-02-14 - [C11 §6.8.6.3: Break not in loop or switch]

Learning: Break statements are rejected outside of loop or switch statements. This is tricky because standalone `if` statements or simple function bodies are not valid targets for `break`. A dedicated test ensures that `SemanticError::BreakNotInLoop` is correctly thrown in these cases, preventing miscompilation. Action: Add `guardian_break_not_in_loop_or_switch.rs` to validate this invariant, asserting correct phase (`SemanticLowering`), message, and precise line/column spans.
2026-06-22 - [C11 §6.8.6.2: Continue not in loop]

Learning: Continue statements are rejected outside of loop statements. This is tricky because standalone `if` statements, `switch` statements, or simple function bodies are not valid targets for `continue`. A dedicated test ensures that `SemanticError::ContinueNotInLoop` is correctly thrown in these cases, preventing miscompilation.
Action: Add `guardian_continue_not_in_loop.rs` to validate this invariant, asserting correct phase (`Mir`), message, and precise line/column spans.

2026-06-26 - [C11 §6.8.4.2: Case and Default not in Switch]

Learning: `case` and `default` statements must be enclosed within a `switch` statement. A dedicated test ensures that `SemanticError::CaseNotInSwitch` is correctly thrown in these cases (like standalone or nested inside an `if` but outside a `switch`), preventing miscompilation. We also fixed a span issue where the diagnostic previously pointed to the inner statement instead of the actual `case` or `default` keyword.
Action: Add `guardian_case_not_in_switch.rs` to validate this invariant, asserting correct phase (`Mir`), message, and precise line/column spans.

2026-07-01 - [Invalid Storage Class for Function Constraints]

Learning: C11 restricts which storage class specifiers can be used with function declarations. `auto` and `register` are invalid for function declarations in all scopes, `_Thread_local` is not allowed for functions, and block-scope function declarations cannot have `static` linkage. The compiler correctly enforced these during semantic lowering via `SemanticError::InvalidStorageClassForFunction` and `SemanticError::ThreadLocalNotAllowed`, but lacked a dedicated integration test specifically targeting all of these function-specific storage class constraints.
Action: Add `guardian_invalid_storage_class_for_function.rs` to explicitly validate these rejections, asserting the correct error kind, phase (`SemanticLowering`), and precise span.

## 2024-07-06 - Variadic Function Argument Validation

Learning: The `SemanticAnalyzer` in Cendol failed to validate that a call to a variadic function passes at least the minimum number of arguments required by its non-variadic parameters. This allowed a call like `void f(int x, ...); f();` to pass semantic validation but later crash during MIR validation with an `IllegalOperation("Call to function f arg count mismatch")` because the argument count didn't match the required parameters.

Action: Ensure semantic checks always enforce the minimum required argument count for variadic functions. Added tests to explicitly guard `SemanticError::InvalidNumberOfArguments` for variadic functions with too few arguments.

2026-07-08 - [C11 §6.8.6.3: Break not in loop or switch]

Learning: Break statements must be enclosed within a loop or switch statement. This constraint is properly validated during the `CompilePhase::Mir` by traversing the AST to detect breaks outside valid blocks. A standalone `break`, or one inside an `if` but outside a loop or switch, will throw `SemanticError::BreakNotInLoop`. Adding specific unit tests ensures that the phase correctly catches and rejects this invalid control flow structure.
Action: Add `guardian_break_not_in_loop_or_switch.rs` to validate this invariant, ensuring the diagnostic triggers at `CompilePhase::Mir` with the correct error message and specific line/column spans.
2024-05-18 - [Bit-field width and type validation constraints]

Learning: [The C standard sets specific rules regarding bit-fields. Validation points for bit-fields during the semantic lowering phase are extremely specific. For instance, C23 and earlier standards prohibit an `_Atomic` type in a bitfield entirely and explicitly prevent zero-width bit-fields from having an assigned name. Invalid types (like floats) and width declarations that are non-constant expressions or exceed the types underlying size will also error. To capture the full spectrum of restrictions, exhaustive combinations must be checked in the negative tests for these invariants.] Action: [Ensure that any validation for memory layouts heavily constrains its testing for corner cases—such as zero-width bit-fields versus named zero-width bit-fields. Semantic tests shouldn't just check 'does not compile'; they must explicitly verify the error spans and messages (e.g., 'zero-width bit-field shall not specify a declarator', 'bit-field shall not have an atomic type', and 'width of bit-field exceeds width of its type'). Tests added in `guardian_bitfield_constraints.rs` capture these diagnostic expectations safely.]
