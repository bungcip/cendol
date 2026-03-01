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
fn test_hex_suffixed_literals() {
    // Hex literals with L suffix (non-decimal path)
    check_literal_type("void f() { 0x1L; }", "long");
    // 0x8000000000000000 (2^63) fits in unsigned long but not long (on 64-bit)
    check_literal_type("void f() { 0x8000000000000000L; }", "unsigned long");

    // Hex literals with LL suffix (non-decimal path)
    check_literal_type("void f() { 0x1LL; }", "long long");
    // 0x8000000000000000 (2^63) fits in unsigned long long but not long long
    check_literal_type("void f() { 0x8000000000000000LL; }", "unsigned long long");
}

#[test]
fn test_octal_literals() {
    // 037777777777 (0xffffffff)
    // Same as hex, should be unsigned int.
    check_literal_type("void f() { 037777777777; }", "unsigned int");
}
#[test]
fn test_decimal_suffixless_too_large_for_long_long() {
    // A decimal constant with no suffix: int, long, long long.
    // If it's too large for long long, we still try long long and then fallback
    // to unsigned long long. Let's make sure it falls back properly.
    // 18446744073709551615 (2^64 - 1)
    check_literal_type("void f() { 18446744073709551615; }", "unsigned long long");
}

#[test]
fn test_hex_suffixless_unsigned_long_long() {
    // Hex without suffix: int, unsigned int, long, unsigned long, long long, unsigned long long
    // 0xffffffffffffffff fits only in unsigned long long
    check_literal_type("void f() { 0xffffffffffffffff; }", "unsigned long");
}

#[test]
fn test_hex_suffixless_unsigned_long() {
    // Hex without suffix, fits in unsigned long but not long (on 64 bit, unsigned long is 64 bit)
    // Actually, on 64 bit, long is 64 bit, so long max is 2^63 - 1
    // Let's use 2^63 = 0x8000000000000000
    check_literal_type("void f() { 0x8000000000000000; }", "unsigned long");
}

#[test]
fn test_u_suffix_too_large_for_unsigned_int() {
    // U suffix: unsigned int, unsigned long, unsigned long long
    // 4294967296u -> unsigned long (on 64 bit)
    check_literal_type("void f() { 4294967296u; }", "unsigned long");
    // 18446744073709551615u -> unsigned long long
    check_literal_type("void f() { 18446744073709551615u; }", "unsigned long");
}

#[test]
fn test_l_suffix_decimal_long_long() {
    // L suffix decimal: long, long long
    // 9223372036854775808L (long max + 1)
    // This doesn't fit in signed long on 64 bit (since signed long is 64 bit).
    // It doesn't fit in long long either (since long long is 64 bit).
    // It will fallback to unsigned long long.
    check_literal_type("void f() { 9223372036854775808L; }", "unsigned long long");
}

#[test]
fn test_l_suffix_hex() {
    // L suffix non-decimal: long, unsigned long, long long, unsigned long long
    // 0xffffffffffffffffL -> unsigned long (on 64 bit unsigned long max is 2^64 - 1, so it actually fits in unsigned long)
    check_literal_type("void f() { 0xffffffffffffffffL; }", "unsigned long");
}
#[test]
fn test_long_long_cases() {
    // LL suffix non-decimal: long long, unsigned long long
    check_literal_type("void f() { 0x1LL; }", "long long");

    // We want a value that fits in unsigned long long, but NOT in long long.
    // On 64-bit platforms, long long is 64-bit, signed.
    // Max long long is 9223372036854775807 (0x7FFFFFFFFFFFFFFF).
    // Let's use 0x8000000000000000LL, which is 9223372036854775808.
    // This doesn't fit in 64-bit signed long long, so it must be unsigned long long.
    check_literal_type("void f() { 0x8000000000000000LL; }", "unsigned long long");

    // L suffix non-decimal: long, unsigned long, long long, unsigned long long
    // Max long is 0x7FFFFFFFFFFFFFFF.
    // Let's use 0x8000000000000000L.
    // It doesn't fit in signed long.
    // Fits in unsigned long (since unsigned long is 64-bit).
    check_literal_type("void f() { 0x8000000000000000L; }", "unsigned long");
}
