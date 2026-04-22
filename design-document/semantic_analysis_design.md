# Semantic Analysis Design

## Overview

Semantic analysis is the process of validating the program's logic and types. It operates on the semantically resolved `Ast` produced by the lowering phase. The primary output is a `SemanticInfo` side table that maps AST nodes to their resolved properties (types, value categories, etc.).

## Core Responsibilities

1. **Type Validation**: Ensure operands are compatible for all operations (arithmetic, logical, assignments).
2. **Implicit Conversion Tracking**: Identify where the C standard requires implicit conversions (integer promotion, usual arithmetic conversions, array-to-pointer decay) and record them.
3. **Value Category Analysis**: Determine if an expression is an `LValue` (modifiable or not) or an `RValue`.
4. **Control Flow Validation**: Enforce rules for `break`, `continue`, `goto`, and `return` (e.g., `break` must be inside a loop or switch).
5. **Constant Evaluation**: Evaluate constant expressions at compile-time (required for array sizes, enum constants, and `_Static_assert`).

## The `SemanticAnalyzer`

The analyzer (in `src/semantic/analyzer.rs`) uses a visitor-like pattern to traverse the `Ast`.

### 1. Expression Analysis
For every expression node, the analyzer:
- Visits sub-expressions.
- Performs type inference based on operator rules.
- Checks constraints (e.g., cannot take the address of a register variable).
- Propagates `LValue` status to the parent node.
- Stores the final `QualType` in the `SemanticInfo`.

### 2. Statement Analysis
For statement nodes, the analyzer:
- Checks condition types (must be scalar).
- Manages loop and switch depths to validate jump statements.
- Resolves `goto` targets to their label definitions.

## Type Compatibility and Conversions

C has complex rules for type compatibility, especially for pointers and composite types. The analyzer leverages the `TypeRegistry` and its own conversion logic to:
- Handle pointer assignment rules (including `void*` and qualifiers).
- Perform "usual arithmetic conversions" to find a common type for binary operators.
- Record implicit casts (e.g., `int` to `float`) so the codegen can emit the correct instructions.

## Constant Expression Evaluation

The `ConstEvalCtx` (in `src/semantic/const_eval.rs`) provides a specialized execution environment for C constant expressions. It is used during analysis to:
- Compute the values of `enum` constants.
- Determine the length of array types (if not a VLA).
- Validate `_Static_assert` conditions.
- Compute branch targets for `switch` statements (`case` values).

## Error Reporting

The semantic analyzer is the primary source of compiler errors. It reports:
- **Type Mismatches**: e.g., assigning a struct to an integer.
- **Symbol Errors**: e.g., using an undeclared variable (already largely handled by the lowering phase).
- **Constraint Violations**: e.g., applying `sizeof` to an incomplete type or function.
- **Standard-Specific Violations**: e.g., using C23 features in C11 mode.