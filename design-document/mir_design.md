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

`MirStmt` represents side-effect operations:

```rust
pub enum MirStmt {
    Assign(Place, Rvalue),
    Store(Operand, Place),
    Call(CallTarget, Vec<Operand>),
    Alloc(Place, TypeId),
    Dealloc(Operand),
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
    BinaryOp(BinaryOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
    Cast(TypeId, Operand),
    PtrAdd(Operand, Operand),
    PtrSub(Operand, Operand),
    PtrDiff(Operand, Operand),
    StructLiteral(Vec<(usize, Operand)>),
    ArrayLiteral(Vec<Operand>),
    Load(Operand),
    Call(CallTarget, Vec<Operand>),
}
```

## Type System

The MIR type system is explicit and comprehensive:

```rust
pub enum MirType {
    Void,
    Bool,
    Int {
        is_signed: bool,
        width: u8,
    },
    Float {
        width: u8,
    },
    Pointer {
        pointee: TypeId,
    },
    Array {
        element: TypeId,
        size: usize,
        layout: MirArrayLayout,
    },
    Function {
        return_type: TypeId,
        params: Vec<TypeId>,
    },
    Record {
        name: NameId,
        fields: Vec<(NameId, TypeId)>,
        is_union: bool,
        layout: MirRecordLayout,
    },
    Enum {
        name: NameId,
        variants: Vec<(NameId, i64)>,
    },
}
```

## Constants

Constant values are explicitly represented:

```rust
pub enum ConstValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
    Zero,
    StructLiteral(Vec<(usize, ConstValueId)>),
    ArrayLiteral(Vec<ConstValueId>),
    GlobalAddress(GlobalId),
    FunctionAddress(MirFunctionId),
    Cast(TypeId, ConstValueId),
}
```

## Variables and Globals

`Local` represents local variables and parameters:

```rust
pub struct Local {
    pub id: LocalId,
    pub name: Option<NameId>,
    pub type_id: TypeId,
    pub is_param: bool,
    pub alignment: Option<u32>,
}
```

`Global` represents global variables:

```rust
pub struct Global {
    pub id: GlobalId,
    pub name: NameId,
    pub type_id: TypeId,
    pub is_constant: bool,
    pub initial_value: Option<ConstValueId>,
    pub alignment: Option<u32>,
}
```

## MIR Generation Process

The MIR generation process transforms the annotated AST into MIR:

1. **Function Lowering**: AST function definitions converted to MIR functions
2. **Basic Block Creation**: Control flow structures converted to basic blocks
3. **Expression Lowering**: Complex expressions broken down into simple operations
4. **Memory Operations**: Explicit allocation and deallocation operations added
5. **Type Checking**: MIR validated for type correctness
6. **Optimization**: Basic optimizations applied to MIR

## Cranelift Mapping

The MIR design facilitates efficient mapping to Cranelift IR:

- Basic blocks map directly to Cranelift blocks
- Operations map to Cranelift instructions
- Types map to Cranelift types
- Memory operations map to Cranelift memory instructions
- Function calls map to Cranelift call instructions

## Validation

MIR includes comprehensive validation to ensure correctness:

- Type consistency validation
- Control flow validation
- Memory safety validation
- Constant folding validation

This MIR design provides a solid foundation for optimization and code generation while maintaining the semantics of the original C program.