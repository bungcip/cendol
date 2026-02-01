use crate::ast::NameId;
use crate::tests::semantic_common::setup_lowering;

fn check_type(source: &str, expected: &str) {
    let (_ast, registry, symbol_table) = setup_lowering(source);
    // Assume variable is named 'x'
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).expect("Symbol 'x' not found");
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(registry.display_qual_type(symbol.type_info), expected);
}

#[test]
fn test_long_int_regr() {
    check_type("long int x;", "long");
}

#[test]
fn test_long_long_int_regr() {
    check_type("long long int x;", "long long");
}

#[test]
fn test_unsigned_long_int_regr() {
    check_type("unsigned long int x;", "unsigned long");
}

#[test]
fn test_signed_long_int_regr() {
    check_type("signed long int x;", "long");
}

#[test]
fn test_short_int_regr() {
    check_type("short int x;", "short");
}

#[test]
fn test_unsigned_short_int_regr() {
    check_type("unsigned short int x;", "unsigned short");
}

#[test]
fn test_complex_combinations() {
    check_type("long unsigned int x;", "unsigned long");
    check_type("int long unsigned x;", "unsigned long");
    check_type("unsigned int long x;", "unsigned long");

    check_type("long long unsigned int x;", "unsigned long long");
    check_type("int unsigned long long x;", "unsigned long long");
}
