# Data Flow Design

## Overview

The transformation of source code into machine code in Cendol involves a sequence of well-defined data structures. Each phase consumes one representation and produces the next.

## Data Flow Pipeline

| Phase | Input | Output | Main Transition |
| :--- | :--- | :--- | :--- |
| **Preprocessing** | Source Bytes | `PPToken` Stream | Text -> Macros/Includes handled |
| **Lexing** | `PPToken` Stream | `Token` Stream | Syntax classification |
| **Parsing** | `Token` Stream | `ParsedAst` | Linear -> Hierarchical (Syntactic) |
| **Lowering** | `ParsedAst` | `Ast` | Syntactic -> Semantic (Symbols/Types) |
| **Analysis** | `Ast` | `SemanticInfo` | Validation & Annotation |
| **MIR Gen** | `Ast` + `SemanticInfo` | `MirModule` | High-level -> Intermediate IR |
| **Codegen** | `MirModule` | Object Bytes | IR -> Machine Code |

## Shared State and Side Tables

Rather than a single monolithic object, Cendol uses several shared components to minimize data copying:

### `SourceManager`
Owned by the driver, borrowed by almost all phases. It manages the underlying file buffers and provides source location to text mapping.

### `TypeRegistry`
Central store for all types. Phases refer to types by `TypeRef` (a 32-bit index), ensuring that type comparisons are just integer comparisons.

### `SymbolTable`
Maps names (`NameId`) to semantic entities (`Symbol`). Each `Symbol` contains its type, storage class, and scope information.

### `SemanticInfo`
A side table populated during analysis. It parallels the `Ast` nodes, providing the types and metadata for every statement and expression without cluttering the primary AST storage.

## Communication between Phases

Each phase is typically an independent "driver" function or struct.
- **Ownership**: The results of a phase (like `Ast`) are typically owned by the compiler driver and passed as a borrow to subsequent phases.
- **Immutability**: Once an AST is constructed, it is rarely modified. Later phases (like Analysis) add information through side tables rather than mutating existing nodes.