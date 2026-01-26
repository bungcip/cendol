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

### MIR-to-Cranelift Lowerer
- `MirToCraneliftLowerer`: Main class for MIR to Cranelift conversion
- Function compilation from MIR to Cranelift functions
- Basic block and instruction mapping
- Type and constant translation

### Code Generation Output
- `ClifOutput`: Enum for different output types (Clif IR, Object files)
- Object file generation for system linking
- Clif IR dump for debugging and analysis

### Validation
- MIR validation before code generation
- Generated code validation
- Type consistency checks

## MIR-to-Cranelift Mapping

### Basic Operations
- `MirStmt::Assign` maps to Cranelift move/copy instructions
- `Rvalue` operations map to corresponding Cranelift instructions
- `Terminator` operations map to Cranelift control flow instructions

### Control Flow
- MIR basic blocks map to Cranelift blocks
- `Terminator::Goto` maps to Cranelift jump
- `Terminator::If` maps to Cranelift conditional branch
- `Terminator::Return` maps to Cranelift return

### Function Calls
- `CallTarget::Direct` maps to direct Cranelift calls
- `CallTarget::Indirect` maps to indirect Cranelift calls
- Parameter passing and return value handling
- **Variadic Support**: Special handling for x86_64 SysV variadic calls (reg save area, spill slots)

### Memory Operations
- `Place` operations map to Cranelift memory instructions
- `MirStmt::Alloc` lowers to `malloc` calls
- `MirStmt::Dealloc` lowers to `free` calls
- `MirStmt::Store` maps to Cranelift store

### Context Management
- `MirToCraneliftLowerer`: Main driver for compilation
- `BodyEmitContext`: Context for lowering function bodies
- `EmitContext`: Context for constant emission


## Output Generation

### Object File Creation
- Generation of platform-specific object files
- Symbol table creation and management
- Relocation information for linking
- Debug information inclusion

### Clif IR Output
- Human-readable Clif IR for debugging
- Intermediate representation for analysis
- Optimization opportunity identification

## Performance Optimizations

- Target-specific optimization passes
- Register allocation optimization
- Dead code elimination
- Instruction selection optimization
- Function inlining opportunities

## Error Handling

- Comprehensive MIR validation before generation
- Type consistency checking during mapping
- Target-specific constraint validation
- Diagnostic reporting for generation errors