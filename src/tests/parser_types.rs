use crate::ast::NameId;
use crate::tests::semantic_common::setup_lowering;
use crate::tests::test_utils::run_fail_with_message;

fn check_type(source: &str, expected: &str) {
    let (_ast, registry, symbol_table) = setup_lowering(source);
    // Assume variable is named 'x'
    let (entry, _) = symbol_table
        .lookup_symbol(NameId::from("x"))
        .expect("Symbol 'x' not found");
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(registry.display_qual_type(symbol.type_info), expected);
}

#[test]
fn test_type_combinations() {
    check_type("short int x;", "short");
    check_type("unsigned short int x;", "unsigned short");

    check_type("long int x;", "long");
    check_type("signed long int x;", "long");

    check_type("unsigned long int x;", "unsigned long");
    check_type("long unsigned int x;", "unsigned long");
    check_type("int long unsigned x;", "unsigned long");
    check_type("unsigned int long x;", "unsigned long");

    check_type("long long int x;", "long long");

    check_type("long long unsigned int x;", "unsigned long long");
    check_type("int unsigned long long x;", "unsigned long long");
}

#[test]
fn test_type_specifier_combinations() {
    // Use _Atomic(...) to force the parser's type builder logic (parsed_type_builder.rs)
    // instead of semantic lowering logic, ensuring coverage of merge_parsed_type_specifiers.

    // (Long, Long) via (Long, Int) -> Long + Long
    check_type("_Atomic(long int long) x;", "_Atomic long long");

    // (Int, Long)
    check_type("_Atomic(int long) x;", "_Atomic long");

    // (LongLong, Int)
    check_type("_Atomic(long long int) x;", "_Atomic long long");
    check_type("_Atomic(long long long) x;", "_Atomic long long"); // (LongLong, Long)
    check_type("_Atomic(long long int) x;", "_Atomic long long"); // (LongLong, Int)
    check_type("_Atomic(int long long) x;", "_Atomic long long"); // (Int, LongLong)

    // Redundant
    check_type("_Atomic(signed signed int) x;", "_Atomic int");
    check_type("_Atomic(unsigned unsigned int) x;", "_Atomic unsigned int");

    // Composite + Int
    check_type("_Atomic(unsigned long int) x;", "_Atomic unsigned long"); // (UnsignedLong, Int) or (Unsigned, Long, Int) -> UnsignedLong, Int
    check_type("_Atomic(int unsigned long) x;", "_Atomic unsigned long");
    check_type("_Atomic(signed long int) x;", "_Atomic long");
    check_type("_Atomic(int signed long) x;", "_Atomic long");
    check_type("_Atomic(unsigned long long int) x;", "_Atomic unsigned long long");
    check_type("_Atomic(int unsigned long long) x;", "_Atomic unsigned long long");
    check_type("_Atomic(signed long long int) x;", "_Atomic long long");
    check_type("_Atomic(int signed long long) x;", "_Atomic long long");
    check_type("_Atomic(unsigned short int) x;", "_Atomic unsigned short");
    check_type("_Atomic(int unsigned short) x;", "_Atomic unsigned short");
    check_type("_Atomic(signed short int) x;", "_Atomic short");
    check_type("_Atomic(int signed short) x;", "_Atomic short");

    // Basic Signed/Unsigned/Short/Long combinations
    check_type("_Atomic(int short) x;", "_Atomic short");
    check_type("_Atomic(short int) x;", "_Atomic short");

    check_type("_Atomic(signed int) x;", "_Atomic int");
    check_type("_Atomic(int signed) x;", "_Atomic int");

    check_type("_Atomic(signed char) x;", "_Atomic signed char");
    check_type("_Atomic(char signed) x;", "_Atomic signed char");

    check_type("_Atomic(signed short) x;", "_Atomic short");
    check_type("_Atomic(short signed) x;", "_Atomic short");

    check_type("_Atomic(signed long) x;", "_Atomic long");
    check_type("_Atomic(long signed) x;", "_Atomic long");

    check_type("_Atomic(signed long long) x;", "_Atomic long long");
    check_type("_Atomic(long long signed) x;", "_Atomic long long");

    check_type("_Atomic(unsigned int) x;", "_Atomic unsigned int");
    check_type("_Atomic(int unsigned) x;", "_Atomic unsigned int");

    check_type("_Atomic(unsigned char) x;", "_Atomic unsigned char");
    check_type("_Atomic(char unsigned) x;", "_Atomic unsigned char");

    check_type("_Atomic(unsigned short) x;", "_Atomic unsigned short");
    check_type("_Atomic(short unsigned) x;", "_Atomic unsigned short");

    check_type("_Atomic(unsigned long) x;", "_Atomic unsigned long");
    check_type("_Atomic(long unsigned) x;", "_Atomic unsigned long");

    check_type("_Atomic(unsigned long long) x;", "_Atomic unsigned long long");
    check_type("_Atomic(long long unsigned) x;", "_Atomic unsigned long long");

    // Complex types
    check_type("_Atomic(_Complex float) x;", "_Atomic _Complex float");
    check_type("_Atomic(float _Complex) x;", "_Atomic _Complex float");
    check_type("_Atomic(_Complex double) x;", "_Atomic _Complex double");
    check_type("_Atomic(double _Complex) x;", "_Atomic _Complex double");
    check_type("_Atomic(_Complex long double) x;", "_Atomic _Complex long double");
    check_type("_Atomic(long double _Complex) x;", "_Atomic _Complex long double");
}

#[test]
fn test_conflict_cast() {
    let src = "void foo() { (int struct S { int x; }) 0; }";
    run_fail_with_message(src, "single type specifier");
}
