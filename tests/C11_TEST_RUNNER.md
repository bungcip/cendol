# C11 Features Test Runner

This test runner uses `cargo insta` to comprehensively test C11 language support in the cendol C compiler based on the `--dump-parser` functionality.

## Test Coverage

The test suite covers all major C11 features:

### ✅ Working Features
- **Basic Enums**: Named and anonymous enum declarations and usage
- **C11 Booleans**: `_Bool` type support
- **Thread Local Storage**: `_Thread_local` keyword support
- **Complex Numbers**: `_Complex` type support
- **Unicode Strings**: UTF-8 (`u8""`) and wide string (`L""`) literals
- **Alignas/Alignof**: Alignment specifiers and operators
- **Generic Selection**: `_Generic` keyword for type-based selection
- **Noreturn**: `_Noreturn` function attribute

### ⚠️ Partially Working Features
- **Restrict Pointers**: Recognized but not fully parsed in function parameters
- **Static Assert**: Keyword recognized but not fully implemented in parser
- **Atomic Types**: `_Atomic` keyword support varies

### ❌ Not Yet Implemented
- Some advanced C11 features may require parser enhancements

## Running the Tests

### Run All C11 Tests
```bash
cargo test test_c11_
```

### Run Specific Test
```bash
cargo test test_basic_enum
cargo test test_c11_booleans
cargo test test_c11_restrict
# etc.
```

### Update Snapshots
```bash
cargo insta accept
```

### Review Snapshots (Interactive)
```bash
cargo insta review
```

## Test Implementation

Each test:
1. Creates a temporary C source file with specific C11 features
2. Runs `cargo run -- --dump-parser <test_file.c>`
3. Captures the AST output 
4. Uses `insta::assert_snapshot!` to validate against stored snapshots

## Files Created

- `tests/c11_features.rs`: Main test suite with 13 comprehensive test cases
- `tests/snapshots/`: Auto-generated snapshot files for regression testing
- `tests/fixtures/`: Temporary test file directory

## Example Output

When tests pass, you get clean AST dumps like:
```
1: EnumConstant(RED, auto)
2: EnumConstant(GREEN, auto) 
3: EnumConstant(BLUE, auto)
4: Declaration(1 specifiers, init_declarators = [Identifier("c", TypeQualifiers(0x0), None) Some(Expression(1))])
5: LiteralInt(0)
6: Return(5)
7: CompoundStatement([4, 6])
8: FunctionDef(1 specifiers, body=7)
9: TranslationUnit([8])
```

## Continuous Integration

The test runner is designed for CI/CD integration:
- Tests are deterministic
- Snapshots catch regressions automatically
- Failed tests show exactly what changed
- Easy to update expectations with `cargo insta accept`

## Adding New C11 Tests

To add a new C11 feature test:

1. Add a new test function to `tests/c11_features.rs`
2. Include the C11 syntax you want to test
3. Run the test once to generate the snapshot
4. Review and accept the snapshot with `cargo insta accept`

The test framework will then automatically validate that future changes don't break the expected AST output for that C11 feature.