# Changelog

All notable changes to this project will be documented in this file.

## [0.3.0] - 2026-05-12

### Added

- **Features & C23 Support**:
  - `constexpr` for constant expressions and `auto` type deduction.
  - `#embed` preprocessor directive for binary data inclusion.
  - `typeof` and `typeof_unqual` operators.
  - `nullptr` and boolean literals (`true`, `false`).
  - Unicode string and character literals (`u8`, `u`, `U`).
  - Binary literals (`0b`) and digit separators (`'`).
  - `#elifdef` and `#elifndef` preprocessor directives.
  - Empty initializers for arrays of unknown size.
- **GNU Extensions & Builtins**:
  - `__auto_type` and `__builtin_choose_expr` support.
  - Intrinsics: `__builtin_complex`, `__builtin_memcpy`, `__builtin_memcmp`, `__builtin_trap`, `__builtin_unreachable`, `__builtin_constant_p`, `__builtin_prefetch`.
  - Math/Bitwise builtins: `__builtin_fabs` family, `__builtin_ffs` family.
  - Preprocessor macros: `__has_c_attribute`, `__has_include_next`, `__VA_OPT__`.
  - Support for GNU `aligned`, `packed` attributes, and zero-length arrays.
- **C11 Compliance**:
  - Enforced C11 static array declarator, compound literal, and variable-length array (VLA) constraints.
  - Stricter validation for `_Generic` distinctness, bit-field sizes, and pointer arithmetic completeness.
  - Hardened function parameter compatibility, alignment (`_Alignas`) rules, and type alias consistency.
- **Optimizations**:
  - Vastly accelerated macro expansion, token caching, and stringification using `Vec` stacks and `Cow`.
  - SIMD-accelerated (`memchr`) line-start calculation and token skipping in the lexer.
  - Reduced memory footprint by optimizing `QualType` size via `NonZero` and reducing redundant clones.
  - Switched to `hashbrown` and optimized `TypeRegistry` hot paths, semantic analysis, and preprocessor hide-set management for significant compilation speedups.
- **Infrastructure**:
  - Upgraded `cranelift` backend to 0.131.
  - Added support for compiling `sqlite`, `libpng`, and `zlib` in the real-world test suite.
  - Added CLI options: `--version`, `--timing`, `-w` (suppress all warnings), and support for `-Wno-*` flags.

### Fixed

- Corrected macro expansion bugs including self-referential macros, deferred macro expansion, and infinite recursion during token pasting.
- Addressed various miscompilations regarding floating-point casts, long double types, bitfields, alignment, and global variable initialization.
- Fixed compiler hangs/crashes in switch statements with large numbers and out-of-bounds float-to-integer conversions.
- Resolved C11 typedef shadowing and scope visibility issues inside declaration lists.
- Fixed `sizeof` operator evaluation on variable-length arrays and compound literals.

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
