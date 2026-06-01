use crate::tests::test_utils::run_fail_with_message;

/// all declarator/declaration/statement parser error is in here
#[test]
fn test_parser_errors() {
    let cases = [
        // A. Declarator errors
        ("int foo()();", "Declaration not allowed in this context"),
        ("int foo()[5];", "Declaration not allowed in this context"),
        ("int foo[5]();", "Declaration not allowed in this context"),
        ("int (***+x);", "expected ), found +"),
        ("void foo(int +);", "expected ), found +"),
        ("void foo(int (int +));", "expected ), found int"),
        ("void foo(int (int x +));", "expected ), found int"),
        ("void foo(int (+));", "expected ), found +"),
        ("void foo(+);", "expected ), found +"),
        ("void foo(+x);", "expected ), found +"),
        ("void foo(int x, +);", "expected ), found +"),
        ("void foo(){foo(1}", "expected )"),
        ("void foo() { int x[] = {1, 2; }", "expected }"),
        ("void foo() { struct S { int x; ", "expected }"),
        ("void foo(int x, int y", "expected )"),
        ("void foo(int ( + ));", "expected ), found +"),
        ("void foo(int ..., int);", "expected ), found ..."),
        // B. Context-specific "expected identifier" errors
        ("void foo() { struct S s; s . 1; }", "expected identifier, found 1"),
        ("void foo() { struct S *s; s->1; }", "expected identifier, found 1"),
        (
            "void foo() { __builtin_offsetof(struct S, 1); }",
            "expected identifier, found 1",
        ),
        ("enum E { 1 };", "expected identifier, found 1"),
        (
            "struct S { int x; }; void foo() { struct S s = { . + = 1 }; }",
            "expected identifier, found +",
        ),
        ("void foo() { goto 1; }", "expected identifier, found 1"),
        // C. Declaration/Statement errors
        (
            "int foo() { int 1; }",
            "expected Expected declarator or identifier after type specifier",
        ),
        // D. Type specifier errors
        ("long", "Unexpected token"),
        ("_Atomic(", "Unexpected token"),
        ("void foo() { (int struct S { int x; }) 0; }", "single type specifier"),
        // E. Hex float validation (lexical error in constant parsing)
        ("void foo() { double x = 0x1.0p; }", "invalid token"),
        // F. Coverage for specific "expected" messages in parse_decl
        (
            "void foo() { struct S { int x; } 123; }",
            "Expected ';' after struct/union definition",
        ),
        ("void foo() { enum E { A } 123; }", "Expected ';' after enum definition"),
        ("void foo() { extern 123; }", "Expected type specifiers"),
        ("void foo(int __attribute__ noreturn);", "expected ), found int"),
        ("int __attribute__((noreturn))", "Expected type specifiers"),
        ("int ", "Expected declarator or identifier after type specifier"),
        ("int x[10 ;", "expected ], found ;"),
        ("void foo(int ( * );", "expected ), found ;"),
        ("void foo(int ( * [ ] );", "expected ), found ;"),
        ("void foo(int x : 5);", "expected ), found :"),
        ("void foo(int : 5);", "expected ), found :"),
        ("int x : 5;", "expected ';' after declaration, found :"),
        // G. Coverage for synchronization and lexer errors
        (r#"#error "custom error""#, "custom error"),
        ("#endif", "Unmatched #endif"),
        (r#"#error "fail""#, "fail"),
        ("int x = +; }", "found ;"),
        ("int x =", "found end of file"),
        ("_Alignas(", "found end of file"),
        ("void foo() { (", "found end of file"),
        ("void foo() { { int x = +; } }", "found ;"),
        ("[[maybe_unused]]", "found ["),
        ("int _Atomic(int[5]) x;", "array"),
        ("int _Atomic(int(void)) x;", "function"),
        ("int _Atomic(int[5]) x;", "array"),
        ("int _Atomic(int(void)) x;", "function"),
        ("int _Atomic(int[5]) x;", "specifier cannot be used with array type"),
        (
            "int _Atomic(int(void)) x;",
            "specifier cannot be used with function type",
        ),
        (
            "int _Atomic(_Atomic(int)) x;",
            "specifier cannot be used with atomic type",
        ),
        (
            "int _Atomic(int(void)) x;",
            "specifier cannot be used with function type",
        ),
    ];

    for (source, message) in cases {
        run_fail_with_message(source, message);
    }
}

#[test]
fn test_parse_diag_display_and_eof() {
    use crate::parser::{ParseDiag, ParseError};
    use crate::source_manager::SourceSpan;

    let diag = ParseDiag {
        span: SourceSpan::default(),
        kind: ParseError::UnexpectedEof,
    };
    assert_eq!(diag.to_string(), "Unexpected End of File");
}
