use super::semantic_common::setup_analysis;
use crate::ast::NodeKind;

fn check_literal_type(source: &str, expected_type_str: &str) {
    let (ast, registry, _) = setup_analysis(source);

    // Find the Literal node.
    let mut found = false;
    for (i, kind) in ast.kinds.iter().enumerate() {
        if let NodeKind::Literal(crate::ast::literal::Literal::Int { .. }) = kind {
            let ty = ast.semantic_info.as_ref().unwrap().types[i].expect("Literal type not resolved");
            let ty_str = registry.display_qual_type(ty);
            assert_eq!(ty_str, expected_type_str, "Type mismatch for source: {}", source);
            found = true;
            // We verify the first integer literal we find.
            // Since we construct simple functions with one literal, this is fine.
            break;
        }
    }
    assert!(found, "Literal not found in AST for source: {}", source);
}

#[test]
fn test_hex_literal_unsigned_int() {
    // 0xffffffff (4294967295)
    // Fits in unsigned int (32-bit), but not int (max 2147483647).
    // Base 16 -> allowed to be unsigned int.
    // C11 6.4.4.1 table for Hex/Octal: int, unsigned int, ...
    check_literal_type("void f() { 0xffffffff; }", "unsigned int");
}

#[test]
fn test_hex_literal_int() {
    // 0x7fffffff (2147483647)
    // Fits in int.
    check_literal_type("void f() { 0x7fffffff; }", "int");
}

#[test]
fn test_decimal_literal_int() {
    // 2147483647
    check_literal_type("void f() { 2147483647; }", "int");
}

#[test]
fn test_decimal_literal_long() {
    // 2147483648 (INT_MAX + 1)
    // Decimal constant: int, long int, long long int.
    // Does NOT include unsigned int.
    // So it must be long (if long is 64-bit) or long long.
    // On x86_64 Linux, long is 64-bit.
    check_literal_type("void f() { 2147483648; }", "long");
}

#[test]
fn test_suffixed_literals() {
    check_literal_type("void f() { 1u; }", "unsigned int");
    check_literal_type("void f() { 1U; }", "unsigned int");
    check_literal_type("void f() { 1l; }", "long");
    check_literal_type("void f() { 1L; }", "long");
    check_literal_type("void f() { 1ll; }", "long long");
    check_literal_type("void f() { 1LL; }", "long long");
    check_literal_type("void f() { 1ul; }", "unsigned long");
    check_literal_type("void f() { 1UL; }", "unsigned long");
    check_literal_type("void f() { 1ull; }", "unsigned long long");
    check_literal_type("void f() { 1ULL; }", "unsigned long long");
}

#[test]
fn test_octal_literals() {
    // 037777777777 (0xffffffff)
    // Same as hex, should be unsigned int.
    check_literal_type("void f() { 037777777777; }", "unsigned int");
}
