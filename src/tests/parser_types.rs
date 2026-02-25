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
    let cases = vec![
        ("short int x;", "short"),
        ("unsigned short int x;", "unsigned short"),
        ("long int x;", "long"),
        ("signed long int x;", "long"),
        ("unsigned long int x;", "unsigned long"),
        ("long unsigned int x;", "unsigned long"),
        ("int long unsigned x;", "unsigned long"),
        ("unsigned int long x;", "unsigned long"),
        ("long long int x;", "long long"),
        ("long long unsigned int x;", "unsigned long long"),
        ("int unsigned long long x;", "unsigned long long"),
    ];
    for (source, expected) in cases {
        check_type(source, expected);
    }
}

#[test]
fn test_type_specifier_combinations() {
    // Use _Atomic(...) to force the parser's type builder logic (parsed_type_builder.rs)
    // instead of semantic lowering logic, ensuring coverage of merge_parsed_type_specifiers.

    let cases = vec![
        // (Long, Long) via (Long, Int) -> Long + Long
        ("_Atomic(long int long) x;", "_Atomic long long"),
        // (Int, Long)
        ("_Atomic(int long) x;", "_Atomic long"),
        // (LongLong, Int)
        ("_Atomic(long long int) x;", "_Atomic long long"),
        ("_Atomic(long long long) x;", "_Atomic long long"), // (LongLong, Long)
        ("_Atomic(int long long) x;", "_Atomic long long"),  // (Int, LongLong)
        // Composite + Int
        ("_Atomic(unsigned long int) x;", "_Atomic unsigned long"), // (UnsignedLong, Int) or (Unsigned, Long, Int) -> UnsignedLong, Int
        ("_Atomic(int unsigned long) x;", "_Atomic unsigned long"),
        ("_Atomic(signed long int) x;", "_Atomic long"),
        ("_Atomic(int signed long) x;", "_Atomic long"),
        ("_Atomic(unsigned long long int) x;", "_Atomic unsigned long long"),
        ("_Atomic(int unsigned long long) x;", "_Atomic unsigned long long"),
        ("_Atomic(signed long long int) x;", "_Atomic long long"),
        ("_Atomic(int signed long long) x;", "_Atomic long long"),
        ("_Atomic(unsigned short int) x;", "_Atomic unsigned short"),
        ("_Atomic(int unsigned short) x;", "_Atomic unsigned short"),
        ("_Atomic(signed short int) x;", "_Atomic short"),
        ("_Atomic(int signed short) x;", "_Atomic short"),
        // Basic Signed/Unsigned/Short/Long combinations
        ("_Atomic(int short) x;", "_Atomic short"),
        ("_Atomic(short int) x;", "_Atomic short"),
        ("_Atomic(signed int) x;", "_Atomic int"),
        ("_Atomic(int signed) x;", "_Atomic int"),
        ("_Atomic(signed char) x;", "_Atomic signed char"),
        ("_Atomic(char signed) x;", "_Atomic signed char"),
        ("_Atomic(signed short) x;", "_Atomic short"),
        ("_Atomic(short signed) x;", "_Atomic short"),
        ("_Atomic(signed long) x;", "_Atomic long"),
        ("_Atomic(long signed) x;", "_Atomic long"),
        ("_Atomic(signed long long) x;", "_Atomic long long"),
        ("_Atomic(long long signed) x;", "_Atomic long long"),
        ("_Atomic(unsigned int) x;", "_Atomic unsigned int"),
        ("_Atomic(int unsigned) x;", "_Atomic unsigned int"),
        ("_Atomic(unsigned char) x;", "_Atomic unsigned char"),
        ("_Atomic(char unsigned) x;", "_Atomic unsigned char"),
        ("_Atomic(unsigned short) x;", "_Atomic unsigned short"),
        ("_Atomic(short unsigned) x;", "_Atomic unsigned short"),
        ("_Atomic(unsigned long) x;", "_Atomic unsigned long"),
        ("_Atomic(long unsigned) x;", "_Atomic unsigned long"),
        ("_Atomic(unsigned long long) x;", "_Atomic unsigned long long"),
        ("_Atomic(long long unsigned) x;", "_Atomic unsigned long long"),
        // Complex types
        ("_Atomic(_Complex float) x;", "_Atomic _Complex float"),
        ("_Atomic(float _Complex) x;", "_Atomic _Complex float"),
        ("_Atomic(_Complex double) x;", "_Atomic _Complex double"),
        ("_Atomic(double _Complex) x;", "_Atomic _Complex double"),
        ("_Atomic(_Complex long double) x;", "_Atomic _Complex long double"),
        ("_Atomic(long double _Complex) x;", "_Atomic _Complex long double"),
    ];

    for (source, expected) in cases {
        check_type(source, expected);
    }
}

#[test]
fn test_conflict_cast() {
    let src = "void foo() { (int struct S { int x; }) 0; }";
    run_fail_with_message(src, "single type specifier");
}
