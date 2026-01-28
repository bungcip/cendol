# Changelog

All notable changes to this project will be documented in this file.

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
