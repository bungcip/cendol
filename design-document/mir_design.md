# Mid-level Intermediate Representation (MIR) Design

## Overview

The MIR (Mid-level Intermediate Representation) is a typed, explicit representation of C11 programs designed for semantic analysis, optimization, and code generation. Unlike the AST which represents source syntax, MIR represents the semantics of the program in a form that is easy to analyze and transform for the Cranelift backend.

## Key Design Principles

1. **Typed Representation**: All entities have explicit types with no implicit conversions
2. **Explicit Semantics**: All C semantics are made explicit (no implicit operations)
3. **Cranelift-Friendly**: Designed to map efficiently to Cranelift IR
4. **Non-SSA Form**: Uses basic blocks with explicit control flow rather than SSA
5. **Memory Safety**: Explicit memory operations with clear ownership semantics

## MIR Structure

The MIR is composed of:

- `MirModule`: Top-level container for MIR
- `MirFunction`: Represents C functions in MIR
- `MirBlock`: Basic blocks with statements and terminators
- `MirStmt`: Side-effect operations within blocks
- `Terminator`: Control flow operations
- `Place`: Storage locations (variables, memory)
- `Operand`: Values used in operations
- `Rvalue`: Right-hand side values in assignments
- `MirType`: Type system for MIR
- `ConstValue`: Constant values
- `Local`: Local variables and parameters
- `Global`: Global variables

## Core Components

### Module and Functions

`MirModule` is the top-level container that holds all functions, globals, types, and constants:

```rust
pub struct MirModule {
    pub id: MirModuleId,
    pub functions: Vec<MirFunctionId>,
    pub globals: Vec<GlobalId>,
    pub types: Vec<MirType>,
    pub constants: Vec<ConstValue>,
}
```

`MirFunction` represents C functions with explicit type information:

```rust
pub struct MirFunction {
    pub id: MirFunctionId,
    pub name: NameId,
    pub return_type: TypeId,
    pub params: Vec<LocalId>,
    pub kind: MirFunctionKind,
    pub is_variadic: bool,
    pub locals: Vec<LocalId>,
    pub blocks: Vec<MirBlockId>,
    pub entry_block: Option<MirBlockId>,
}
```

### Basic Blocks and Control Flow

`MirBlock` contains statements and a terminator:

```rust
pub struct MirBlock {
    pub id: MirBlockId,
    pub statements: Vec<MirStmtId>,
    pub terminator: Terminator,
}
```

`Terminator` handles control flow:

```rust
pub enum Terminator {
    Goto(MirBlockId),
    If(Operand, MirBlockId, MirBlockId),
    Return(Option<Operand>),
    Unreachable,
}
```

### Operations and Values

### Operations and Values

`MirStmt` represents side-effect operations:

```rust
pub enum MirStmt {
    Assign(Place, Rvalue),
    Store(Operand, Place),
    Call {
        target: CallTarget,
        args: Vec<Operand>,
        dest: Option<Place>,
    },
    Alloc(Place, TypeId),
    Dealloc(Operand),
    // Builtin variadic operations
    BuiltinVaStart(Place, Operand),
    BuiltinVaEnd(Place),
    BuiltinVaCopy(Place, Place),
}
```

`Place` represents storage locations:

```rust
pub enum Place {
    Local(LocalId),
    Deref(Box<Operand>),
    Global(GlobalId),
    StructField(Box<Place>, /* struct index */ usize),
    ArrayIndex(Box<Place>, Box<Operand>),
}
```

`Operand` represents values used in operations:

```rust
pub enum Operand {
    Copy(Box<Place>),
    Constant(ConstValueId),
    AddressOf(Box<Place>),
    Cast(TypeId, Box<Operand>),
}
```

`Rvalue` represents right-hand side values:

```rust
pub enum Rvalue {
    Use(Operand),
    BinaryIntOp(BinaryIntOp, Operand, Operand),
    BinaryFloatOp(BinaryFloatOp, Operand, Operand),
    UnaryIntOp(UnaryIntOp, Operand),
    UnaryFloatOp(UnaryFloatOp, Operand),
    Cast(TypeId, Operand),
    PtrAdd(Operand, Operand),
    PtrSub(Operand, Operand),
    PtrDiff(Operand, Operand),
    StructLiteral(Vec<(usize, Operand)>),
    ArrayLiteral(Vec<Operand>),
    Load(Operand),
    BuiltinVaArg(Place, TypeId),
}
```

### Simplified Data Structures

MIR is built upon a few core enums and structs that ensure type safety and explicit behavior:

- **`MirStmt`**: Assignments (`Assign`), stores (`Store`), function calls (`Call`), and variadic builtins (`BuiltinVaStart`, etc.).
- **`Place`**: Represents memory or storage locations: `Local`, `Global`, `Deref`, `StructField`, `ArrayIndex`.
- **`Operand`**: Values used in operations: `Copy(Place)`, `Constant`, `AddressOf(Place)`, `Cast`.
- **`Rvalue`**: RHS values: `BinaryIntOp`, `BinaryFloatOp`, `UnaryIntOp`, `UnaryFloatOp`, `PtrAdd`/`PtrSub`/`PtrDiff`, `Load(Operand)`.
- **`Terminator`**: Basic block exits: `Goto`, `If`, `Return`, `Unreachable`.

### IR Invariants and Validation

The MIR includes a strict validation pass (`src/mir/validation.rs`) that runs before code generation. It ensures:
1. **Type Consistency**: Both sides of an assignment must have identical MIR types.
2. **Explicit Conversions**: No implicit casts; all type changes must use `Operand::Cast`.
3. **Control Flow Integrity**: All blocks must end with a valid terminator, and branch targets must exist.
4. **Pointer Safety**: Address-of and dereference operations are checked for type correctness.

## MIR Generation

The `MirGen` component (`src/codegen/mir_gen.rs`) transforms the annotated `Ast` into `MirModule`. It performs:
- **Expression Flattening**: Complex nested expressions are broken into sequences of `MirStmt`s.
- **Explicit Casting**: Implicit conversions recorded during semantic analysis are turned into explicit `Rvalue::Cast` or `Operand::Cast` operations.
- **Control Flow Lowering**: High-level loops and conditionals are lowered into basic blocks and terminators.