# GNU Extensions Test Suite

This test suite evaluates the C compiler's handling of GNU extensions, ensuring they compile under GNU mode (`-std=gnu11`) and correctly fail with non-standard extension errors under strict mode (`-std=c11 --pedantic-errors`).

## 1. typeof
**Description**: The `typeof` operator allows retrieving the type of an expression or variable.
**C code snippet**:
```c
int main(void) { int a = 5; typeof(a) b = 6; return b - 6; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 2. Statement expressions
**Description**: Statement expressions `({ ... })` allow evaluating a compound statement as an expression.
**C code snippet**:
```c
int main(void) { int a = ({ int b = 5; b; }); return a - 5; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 3. __attribute__
**Description**: GCC variable attributes like `__attribute__((unused))` allow specifying special properties. Because `__attribute__` is in the reserved namespace, the compiler should not reject it even in strict standard mode.
**C code snippet**:
```c
int main(void) { int a __attribute__((unused)); return 0; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
✅ Compiles with --pedantic-errors (GCC-compatible behavior)

## 4. Zero-length arrays
**Description**: Allows defining an array of size 0 as the last element of a structure (struct hack).
**C code snippet**:
```c
struct S { int len; int data[0]; }; int main(void) { return 0; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 5. Nested functions
**Description**: Allows defining a function within another function. Cendol does not support nested functions in either mode.
**C code snippet**:
```c
int main(void) { int nested(void) { return 0; } return nested(); }
```
**Expected behavior**:
❌ Fails with GNU extensions enabled (Unsupported)
❌ Fails with --pedantic-errors

## 6. Inline assembly
**Description**: Allows embedding inline assembly code using `asm()`. Cendol does not support inline assembly.
**C code snippet**:
```c
int main(void) { asm("nop"); return 0; }
```
**Expected behavior**:
❌ Fails with GNU extensions enabled (Unsupported)
❌ Fails with --pedantic-errors

## 7. GNU designated initializers (ranges)
**Description**: Allows initializing a range of array elements using `[start ... end] = value`.
**C code snippet**:
```c
int main(void) { int a[10] = { [0 ... 9] = 1 }; return a[0] - 1; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 8. GNU designated initializers (obsolete colons)
**Description**: Allows initializing a struct field using `fieldname: value` instead of standard `.fieldname = value`.
**C code snippet**:
```c
struct S { int a; }; int main(void) { struct S s = { a: 1 }; return s.a - 1; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 9. Case ranges
**Description**: Allows specifying a range of values in a switch statement case using `case start ... end:`.
**C code snippet**:
```c
int main(void) { int a = 5; switch(a) { case 1 ... 10: return 0; default: return 1; } }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
❌ Fails with --pedantic-errors

## 10. __builtin_expect
**Description**: Built-in function to provide branch prediction hints. Since it's in the reserved namespace `__builtin_`, it's allowed even in pedantic mode.
**C code snippet**:
```c
int main(void) { int a = 5; if (__builtin_expect(a == 5, 1)) return 0; return 1; }
```
**Expected behavior**:
✅ Compiles with GNU extensions enabled
✅ Compiles with --pedantic-errors
