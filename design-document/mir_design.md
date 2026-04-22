# Mid-level Intermediate Representation (MIR) Design

## Overview

The MIR is a typed, explicit representation of the program after semantic analysis. It simplifies complex C constructs into a form that is easy to validate, optimize, and lower to Cranelift IR.

## Key Design Principles

1. **Typed Representation**: All entities (locals, rvalues, operands) have explicit types.
2. **Explicit Semantics**: Hidden C behaviors (like implicit casts and pointer decay) are made explicit through MIR operations.
3. **Control Flow Graph (CFG)**: Programs are represented as a collection of basic blocks (`MirBlock`) ending with explicit terminators.
4. **Index-based Storage**: Uses `MirFunctionId`, `MirBlockId`, and `MirStmtId` for compact, cache-friendly storage in flattened vectors.

## Data Structures

### `MirModule`
The container for the entire translation unit.
- `functions`: List of defined and declared functions.
- `globals`: Global variables.
- `types`: Deduplicated MIR types.
- `constants`: Interned constant values.

### `MirFunction`
Represents a C function.
- `linkage`: Internal, External, or Import.
- `locals`: All variables including parameters and temporary variables.
- `blocks`: The basic blocks forming the function's CFG.

### `MirBlock`
A sequence of side-effecting statements followed by a single terminator.
- `statements`: A list of `MirStmtId`s.
- `terminator`: `Goto`, `If`, `Return`, `Unreachable`, or `Trap`.

### `MirStmt`
Operations with side effects.
- `Assign(Place, Rvalue)`: Core assignment operation.
- `Call { target, args, dest }`: Function calls.
- `BuiltinVa*`: Variadic builtin operations.
- `AtomicStore`: C11/C23 atomic memory operations.

### `Place`, `Operand`, and `Rvalue`
MIR uses a Three-Address Code style:
- **`Place`**: A memory location or variable (`Local`, `Global`, `Deref`, `StructField`, `ArrayIndex`, `BitField`).
- **`Operand`**: A value used as an input to an operation (`Copy(Place)`, `Constant`, `AddressOf(Place)`, `Cast`).
- **`Rvalue`**: The computation yielding a value (`Use(Operand)`, `BinaryIntOp`, `BinaryFloatOp`, `Load(Operand)`, `PtrAdd`, `StructLiteral`).

## MIR Generation

The generator (`src/codegen/mir_gen.rs`) performs the following transformations:

1. **Statement Lowering**: C statements like `if`, `while`, and `for` are lowered into blocks connected by `Goto` and `If` terminators.
2. **Expression Flattening**: Nested C expressions are broken into a series of assignments to temporary locals.
3. **Explicit Conversions**: Implicit casts from semantic analysis are converted to explicit `Operand::Cast` or `Rvalue::Cast` operations.
4. **Member Access Resolution**: Struct field and array index accesses are converted into `Place` chains with explicit offset calculations when needed.

## Validation

A dedicated validator ensures that the generated MIR is sound:
- **Type Safety**: Operands to a binary operation must have compatible types.
- **CFG Integrity**: Basic blocks must not be empty or have multiple terminators.
- **Local Validity**: Locals must be defined before use.