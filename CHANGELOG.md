# Changelog

All notable changes to this project will be documented in this file.

## [0.2.0] - 2026-02-28

### Added
- **Features**:
  - `_Static_assert` support in declarations, structures, and unions.
  - Bitwise builtins: `__builtin_popcount`, `__builtin_clz`, `__builtin_ctz`.
  - Type compatibility builtin: `__builtin_types_compatible_p`.
  - Initial support for `_Complex` types and arithmetic.
  - `_Generic` expression lvalue support and completeness constraints.
  - Builtin `__builtin_offsetof` and `__PRETTY_FUNCTION__`.
  - Support for `__real__` and `__imag__` operators.
- **C11 Compliance**:
  - Strict enforcement of `_Atomic` and `_Alignas` constraints.
  - Improved `restrict` qualifier and storage class validation.
  - Better `_Noreturn` fall-through analysis for loops with breaks.
  - Enforced C11 enumeration constant range and array declarator constraints.
- **Optimizations**:
  - Significant performance improvements in lexer lookahead and string building.
  - Optimized preprocessor allocation, token pasting, and macro expansion.
  - Reduced memory usage and clones in `TypeRegistry` and Semantic Analyzer hot paths.
- **Infrastructure**:
  - Upgraded `cranelift` backend to 0.128.
  - Integrated `realworld_test.py` for automated validation against real C projects (e.g., Lua).
  - Added CLI options: `-fuse-ld` for linker selection.

### Fixed
- Stack corruption in `ClifGen` and variadic argument lowering.
- Long double ABI and layout issues on x86_64.
- Lexer and preprocessor bugs (token pasting with placemarkers, UCN support).
- Corrected integer literal typing rules (C11 6.4.4.1).
- Improved array size deduction for brace elision and string literals.
- Fixed compiler hangs and crashes on various invalid code patterns.
- Resolved various miscompilations in pointer arithmetic and global initialization.

## [0.1.0] - 2026-01-28

### Added
- Initial release of Cendol as a functional C11 compiler.
- **Frontend**:
  - Full C11 preprocessor with macro expansion and conditional compilation.
  - Lexer and Parser supporting standard C11 syntax.
  - Semantic analysis for type checking and symbol resolution.
- **Backend**:
  - MIR (Mid-level Intermediate Representation) generation.
  - Native code generation using `cranelift`.
  - Automatic linker invocation (via `clang`) to produce executables.
- **Standard Library Support**:
  - Basic support for C standard library headers within `custom-include`.
  - Full variadic function support (`<stdarg.h>`).
