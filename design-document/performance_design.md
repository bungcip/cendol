# Performance Considerations Design Document

## Memory Management Strategy

### Flattened AST Storage
- **Contiguous Vectors**: All AST nodes stored in `Vec<Node>` for superior cache performance
- **Index-based Access**: `NodeRef`, `TypeRef`, `SymbolEntryRef` eliminate pointer indirection
- **Reduced Fragmentation**: Single allocation per AST reduces memory overhead

### Global Symbol Interning
- **Thread-safe Interning**: Using `symbol_table` crate with global symbol table
- **Memory Deduplication**: Identifiers stored once, referenced everywhere
- **Fast Comparisons**: O(1) symbol equality checks

### Packed Data Structures
- **SourceLoc**: 4-byte packed file ID + offset (max 4 MiB files, 1023 files)
- **Bit Flags**: Compact boolean storage using `bitflags` crate
- **NonZero Types**: `Option<ScopeId>` same size as `ScopeId`

## Cache Optimization Techniques

### Data Layout Optimization
- **Flattened Storage**: Eliminates pointer chasing and improves spatial locality
- **Hot Path Optimization**: Frequently accessed data (node kinds, locations) kept together
- **Index-based Navigation**: Predictable memory access patterns

### Memory Access Patterns
- **Sequential Traversal**: AST walking follows contiguous memory access
- **Prefetching Hints**: Compiler hints for predictable access patterns
- **SIMD Opportunities**: Contiguous layout enables vectorized operations

## Algorithmic Complexity

| Phase | Time Complexity | Space Complexity | Key Optimizations |
|-------|----------------|------------------|-------------------|
| Preprocessing | O(n) | O(m) | Token reuse, macro caching |
| Lexing | O(n) | O(1) | UTF-8 processing, symbol interning |
| Parsing | O(n) | O(n) | Pratt parser, flattened AST |
| Semantic Analysis | O(n) | O(s) | Multi-pass analysis, scope caching |
| AST Dumping | O(n) | O(1) | Streaming HTML generation |

## Performance Benchmarks

### Memory Usage Targets
- **AST Storage**: < 2x source file size for typical C code
- **Symbol Table**: Efficient storage with global interning
- **Type Table**: Canonicalized types prevent duplication
- **File Loading**: Direct byte reading with unsafe UTF-8 conversion for performance

### Compilation Speed Goals
- **Linear Scaling**: O(n) performance for all phases
- **Cache-Friendly**: Minimize cache misses through data layout
- **Incremental Potential**: Design supports future incremental compilation

## Profiling and Optimization

### Built-in Performance Monitoring
- **Phase Timing**: Measure time spent in each compilation phase
- **Memory Tracking**: Monitor peak memory usage per phase
- **Cache Analysis**: Profile cache hit/miss ratios

### Optimization Opportunities
- **SIMD Processing**: Vectorized operations on contiguous data
- **Parallel Analysis**: Independent analysis of different scopes
- **Lazy Evaluation**: Defer expensive computations until needed
- **Streaming I/O**: Process large files without full memory load
- **Unsafe UTF-8 Operations**: Skip validation for assumed UTF-8 input
- **Direct Buffer Access**: Eliminate string conversions in preprocessor