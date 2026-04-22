# Performance Design

## Overview

Performance is a first-class citizen in Cendol. The architecture is designed to maximize throughput and minimize memory latency during every phase of compilation.

## Key Strategies

### 1. Flattened Data Structures
Traditional compilers use trees composed of small, individually allocated objects connected by pointers. This leads to:
- Significant memory overhead for pointers.
- Severe cache misses due to memory fragmentation.

Cendol uses **Contiguous Vectors**. Entire ASTs and MIRs are stored in massive buffers. Navigation is done via 32-bit indices (`NodeRef`, `MirBlockId`), which:
- Are half the size of pointers (4 bytes vs 8 bytes).
- Improve cache locality as related nodes are often close in the vector.

### 2. Interning
All strings and names are interned via the `symbol_table` crate. `NameId` comparisons are O(1) integer checks. Similarly, `QualType` and `TypeRef` ensure that the type system is just as efficient.

### 3. Allocation Strategy
- **Arena Allocation**: For data that is only needed during a specific phase, Cendol uses the `bumpalo` crate for fast, bulk-deallocated arena allocation.
- **Side Tables**: Using parallel vectors for metadata (like node types) avoids "Fat Nodes," keeping the primary traversal path as tight as possible.

### 4. Zero-Copy Preprocessing
The preprocessor works directly with the `SourceManager`'s buffers. It avoids creating new strings for tokens whenever possible, instead referencing the original source through spans and string IDs.

### 5. Efficient Diagnostic Generation
While diagnostics must be rich, their *generation* should not slow down the common case of a successful compilation. Cendol defers expensive snippet formatting until the final reporting stage.

## Benchmarking

Cendol benchmarks its phases using `Criterion`. We track:
- **Throughput**: Lines per second.
- **Latency**: Time to first error/result.
- **Memory consumption**: Peak memory usage during compilation of large files (like `sqlite3.c`).

## Current Targets
Cendol is optimized for:
- Large translation units (100k+ lines).
- Modern x86_64 and AArch64 hardware.
- Multi-threaded execution in the code generation phase (Cranelift provides parallel compilation).