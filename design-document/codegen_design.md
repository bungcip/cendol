# Code Generation Design

## Overview

The code generation phase transforms the typed MIR (Mid-level Intermediate Representation) into target code using the Cranelift backend. This phase maps the MIR constructs to Cranelift instructions, performs target-specific optimizations, and generates object files for linking.

## Key Responsibilities

- **MIR-to-Cranelift Mapping**: Convert MIR constructs to equivalent Cranelift IR
- **Target Code Generation**: Generate optimized code for specific target architectures
- **Object File Creation**: Produce object files compatible with system linkers
- **Function Compilation**: Compile individual functions to Cranelift functions
- **Memory Management**: Handle stack and heap allocation in generated code
- **Type Mapping**: Map MIR types to appropriate Cranelift types

## Implementation Approach

The code generation uses:

### Cranelift Backend Integration
- Direct mapping from MIR constructs to Cranelift instructions
- Use of Cranelift's type system and instruction set
- Target-specific optimization passes
- Support for multiple target architectures

### Function Compilation Process
- Individual function compilation from MIR to Cranelift functions
- Basic block translation preserving control flow
- Instruction selection for each MIR operation
- Register allocation and optimization

### Type System Mapping
- MIR types mapped to Cranelift's type system
- Pointer, integer, and floating-point type correspondence
- Struct and array layout preservation
- Function type compatibility

## Core Components

### `ClifGen`
The main orchestrator that manages the Cranelift `ObjectModule` and iterates through the `MirModule`.

### Emission Contexts
- **`EmitContext`**: Handles global state, constants, and global variables.
- **`BodyEmitContext`**: Managed within individual functions to track local variables, basic blocks, and the `FunctionBuilder`.

### Output Generation
The code generator produces a `ClifOutput` enum:
- `ObjectFile(Vec<u8>)`: Ready for linking.
- `ClifDump(String)`: Human-readable Cranelift IR for debugging.

## Implementation Details

- **Type Mapping**: `lower_type` converts `MirType` to Cranelift types (e.g., `I64`, `F32`, or `I8` for various C sizes).
- **Variadic Support**: Specialized logic for SysV x86_64 ABI, including register save areas and overflow buffers.
- **Aggregate Handling**: Structs and arrays are handled via memory operations (`load`/`store`) or packed into registers for small structs.
- **Optimization**: Leverages Cranelift's internal optimization passes and register allocator.

## Validation

- **MIR Validation**: Pre-generation check of MIR invariants.
- **Cranelift Verifier**: Mandatory verification of the generated Clif IR before object file emission.