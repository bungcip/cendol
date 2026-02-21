## Preprocessor Phase

### Overview

The preprocessor is responsible for transforming C source code before it reaches the lexer and parser. It handles macro expansion, conditional compilation, and file inclusion, producing a stream of tokens that represent the preprocessed source. This design mirrors Clang's preprocessor architecture, which emphasizes modularity, efficiency, and standards compliance.

### Key Components

The preprocessor is organized into specialized modules:

1. **preprocessor.rs**: Main orchestrator, directive handling, and macro expansion logic.
2. **pp_lexer.rs**: Specialized lexer for preprocessing tokens (`PPToken`).
3. **interpreter.rs**: Evaluation of `#if` and `#elif` expressions.
4. **header_search.rs**: Logic for resolving `#include` paths.
5. **dumper.rs**: Utility for emitting preprocessed output.

### Data Structures

```rust
/// Preprocessor Configuration
#[derive(Debug, Clone)]
pub struct PPConfig {
    pub include_paths: Vec<PathBuf>,
    pub system_include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>,
    pub standard: CStandard,
}

/// Main Preprocessor
pub struct Preprocessor<'a, 'src> {
    source_manager: &'a mut SourceManager,
    diagnostics: &'src mut DiagnosticEngine,
    macros: HashMap<StringId, MacroInfo>,
    conditionals: Vec<PPConditionalInfo>,
    include_stack: Vec<IncludeStackInfo>,
    header_search: HeaderSearch,
    directive_keywords: DirectiveKeywordTable,
    // ...
}

/// Preprocessing Token
#[derive(Clone, Copy, Debug)]
pub struct PPToken {
    pub kind: PPTokenKind,
    pub flags: PPTokenFlags,
    pub location: SourceLoc,
    pub length: u16,
}

/// PPToken Kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PPTokenKind {
    // Punctuation and operators
    Plus, Minus, Star, Slash, Percent,
    And, Or, Xor, Not, Tilde,
    Less, Greater, LessEqual, GreaterEqual, Equal, NotEqual,
    LParen, RParen, LBracket, RBracket, LBrace, RBrace,
    Dot, Arrow, Comma, Semicolon, Colon, Question,
    Hash, HashHash, Ellipsis,
    // Literals and identifiers
    Ident(StringId),
    StringLiteral(StringId),
    CharLiteral(u64, StringId),
    Number(StringId),
    // Special
    Eof, Eod, Unknown,
}

/// PPToken Flags
bitflags::bitflags! {
    pub struct PPTokenFlags: u8 {
        const LEADING_SPACE = 1 << 0;
        const STARTS_LINE = 1 << 1;
        const PREV_WAS_HASH = 1 << 2;
        const MACRO_EXPANDED = 1 << 3;
        const HAS_INVALID_UCN = 1 << 4;
    }
}
```
```

### Processing Algorithm

1. **Initialization**:
    - Set up source managers and diagnostic engines
    - Initialize built-in macros (__DATE__, __TIME__, __FILE__, etc.)
    - Configure include search paths

2. **Token Stream Processing**:
    - Access source buffer directly from SourceManager (no string conversion)
    - Read tokens from the current lexer
    - Handle directives (#define, #include, #if, etc.)
    - Perform macro expansion on non-directive tokens
    - Manage conditional compilation state

3. **Directive Handling**:
   - **#define**: Parse macro definition and store in macro table
   - **#undef**: Remove macro from table
   - **#include**: Resolve file path and switch input buffers
   - **#if/#ifdef/#ifndef**: Evaluate condition and update conditional stack
   - **#elif/#else/#endif**: Manage conditional compilation flow
   - **#line**: Update source location information using LineMap for diagnostic remapping
   - **#pragma**: Handle implementation-specific directives

4. **Macro Expansion** (Rescan and Further Replacement Algorithm):

The macro expansion follows a two-phase process: argument rescanning and substitution with further rescanning. This is crucial for correct behavior in complex macro interactions.

**Example with Parentheses and Argument Pre-expansion:**

Consider this example that demonstrates argument rescanning and parentheses handling:
```c
#define A(m) m( B(f)
#define B(x) A(x)

#define C(x) < x >

A(C) ) *
```

When expanding `A(C) ) *`, the algorithm proceeds as follows:

**Phase 1: Initial Recognition**
- Input tokens: `A(C) ) *`
- `A` matches function-like macro `A(m)` with argument `C`
- Argument `C` is rescanned (no expansion needed)
- Substitute: `C( B(f)` (from `m( B(f)`)
- Result: `C( B(f) ) *`

**Phase 2: Rescan Result**
- Current tokens: `C( B(f) ) *`
- `C` matches function-like macro `C(x)` with argument `B(f)`
- Argument `B(f)` is rescanned:
  - `B` matches macro `B(x)` with argument `f`
  - Substitute: `A(f)` (from `A(x)`)
  - Result: `A(f)`
- Substitute `C(B(f))` → `< A(f) >`
- Result: `< A(f) > ) *`

**Phase 3: Continue Rescanning**
- Current tokens: `< A(f) > ) *`
- `A(f)` matches function-like macro `A(m)` with argument `f`
- Argument `f` is rescanned (no expansion)
- Substitute: `f( B(f)` (from `m( B(f)`)
- Result: `< f( B(f) > ) *`

**Phase 4: Final Rescanning**
- Current tokens: `< f( B(f) > ) *`
- `B(f)` matches function-like macro `B(x)` with argument `f`
- Argument `f` is rescanned (no expansion)
- Substitute: `A(f)` (from `A(x)`)
- Result: `< f( A(f) > ) *`

**Phase 5: Continue with A(f)**
- `A(f)` matches macro `A(m)` with argument `f`
- Substitute: `f( B(f)`
- Result: `< f( f( B(f) > ) *`

**Phase 6: Continue with B(f)**
- `B(f)` matches macro `B(x)` with argument `f`
- Substitute: `A(f)`
- Result: `< f( f( A(f) > ) *`

This creates an infinite expansion loop, which is prevented by the protection mechanism (`MacroFlags::DISABLED`).

**Final Result:** `< f( B(f) > ) *`

**Token Pasting (`##`) Example:**

Consider this macro that demonstrates token concatenation:
```c
#define CONCAT(a,b) a##b
#define MAKE_NAME(prefix, suffix) CONCAT(prefix, suffix)

MAKE_NAME(var_, 123)
```

**Expansion Process:**
- `MAKE_NAME(var_, 123)` matches function-like macro with arguments `var_` and `123`
- Arguments rescanned: no further expansion
- Substitute: `CONCAT(var_, 123)` (from `CONCAT(prefix, suffix)`)
- Rescan: `CONCAT(var_, 123)` matches macro `CONCAT(a,b)` → `var_##123`
- Token pasting: `##` concatenates `var_` and `123` → `var_123`
- Result: `var_123`

**Data Structure Usage:**
- `MacroInfo`: Stores macro definitions with parameter lists and replacement tokens
- `PPToken`: Manages token sequences during expansion phases
- `Symbol`: Enables fast parameter matching during substitution
- `MacroFlags`: Prevents infinite recursion through the `DISABLED` flag

**Algorithm Flow Diagrams:**

*Argument Rescanning Flow:*
```
A(C) ) * → C( B(f) ) * → < A(f) > ) * → < f( B(f) > ) * → < f( A(f) > ) *
           ↑            ↑             ↑             ↑
        MacroInfo    MacroInfo     MacroInfo     MacroInfo
        A(m)         C(x)           A(m)           B(x)
```

*Token Pasting Flow:*
```
MAKE_NAME(var_, 123) → CONCAT(var_, 123) → var_123
                       ↑                  ↑
                    MacroInfo         Token Pasting
                    CONCAT(a,b)       a##b → ab
```

5. **File Inclusion** (Include Stack Management):

The `#include` directive processes file inclusion with protection against infinite recursion and multiple inclusion.

**Algorithm Steps:**
- **Path Resolution**: Parse include directive (`#include <file>` or `#include "file"`)
  - Quoted includes (`"file"`): Search current directory first, then system paths
  - Angled includes (`<file>`): Search only system include paths from `HeaderSearch`
  - Use `HeaderSearch.search_path`, `system_path`, `quoted_includes`, `angled_includes`

- **File Loading**:
  - Resolve path to absolute path using `PathBuf`
  - Check if file exists and is readable
  - Load file content into `SourceManager.buffers` as `Vec<u8>`
  - Create `FileInfo` with `file_id`, `path`, `size`, `buffer_index`, `line_starts`

- **Include Stack Management**:
  - Push current file state to `include_stack` (`IncludeStackInfo`)
  - Create new `PPLexer` for included file
  - Set `cur_lexer` to new lexer
  - Update `SourceManager` with new file information

- **Infinite Recursion Protection**:
  - Track inclusion depth (maximum ~200 levels)
  - Check for circular dependencies by comparing file paths
  - Use `include_stack` to detect if same file is being included recursively

- **Include Guard Detection**:
  - Monitor `#ifndef`/`#define`/`#endif` patterns at file boundaries
  - Track guard macro names in `HeaderSearch`
  - Skip inclusion if guard macro already defined

**Example:**
```c
// file: main.c
#include "header.h"  // First include - process file
#include "header.h"  // Second include - skip if guarded

// file: header.h
#ifndef HEADER_H
#define HEADER_H
// content
#endif
```

**Data Structure Usage:**
- `HeaderSearch`: Manages search paths and include tracking
- `SourceManager`: Handles file loading and buffer management
- `FileInfo`: Stores per-file metadata
- `IncludeStackInfo`: Tracks include stack state

6. **Line Mapping** (#line Directive Processing):

The `#line` directive allows source code to specify logical source locations that differ from physical file locations. This is commonly used by code generators and preprocessors to provide accurate diagnostic information.

**Algorithm Steps:**
- **Directive Parsing**: Parse `#line` directive syntax: `#line <number> ["filename"]`
  - Extract logical line number (must be positive integer)
  - Extract optional logical filename (string literal)
  - Validate syntax and reject malformed directives

- **LineMap Construction**:
  - Store `LineDirective` entries in sorted order by physical line number
  - Each entry maps a physical line to logical line and optional filename
  - Maintain monotonic ordering for efficient binary search

- **Presumed Location Lookup**:
  - For diagnostic reporting, convert physical locations to presumed locations
  - Use binary search on LineMap entries to find applicable mapping
  - Apply offset calculation: `logical_line = entry.logical_line + (physical_line - entry.physical_line)`

**Example:**
```c
// Physical file: generated.c, physical line 100
#line 50 "original.c"
// Physical line 101, logical line 51 in "original.c"
int x = invalid_syntax; // Error reported at original.c:51
```

**Data Structure Usage:**
- `LineMap`: Stores sorted array of line mapping entries
- `LineDirective`: Represents individual #line directive mappings
- `SourceManager.get_presumed_location()`: Converts physical to logical locations
- `Diagnostic.location`: Uses presumed locations for accurate error reporting

**Performance Characteristics:**
- Binary search lookup: O(log n) where n is number of #line directives
- Memory efficient: Compact storage of mapping entries
- Fast-path for common case: No mappings (direct physical location usage)

### Key Features

- **Standards Compliance**: Full C11 preprocessor support
- **Efficient Token Management**: Reuse of token objects and buffers
- **Modular Architecture**: Separable components for different preprocessing tasks
- **Diagnostic Integration**: Comprehensive error and warning reporting
- **Built-in Macro Support**: Automatic handling of standard predefined macros
- **Include Guard Optimization**: Fast detection of header guards
- **Line Mapping Support**: Efficient #line directive processing with binary search lookups
- **UTF-8 Only**: The preprocessor assumes and only supports UTF-8 encoded source files (no validation performed for performance)
- **Direct Buffer Access**: Works directly with byte buffers from SourceManager, avoiding string conversions
- **Unsafe UTF-8 Operations**: Uses `unsafe` operations assuming UTF-8 validity for maximum performance
- **No Trigraph or Digraph Support**: For simplicity and modern C usage, trigraphs and digraphs will not be supported

### Integration with Compiler Pipeline

The preprocessor produces a token stream that feeds directly into the lexer phase. Source location information is preserved throughout the pipeline, enabling accurate error reporting and debugging. The design ensures that preprocessing is a separate, reusable component that can be tested and optimized independently.