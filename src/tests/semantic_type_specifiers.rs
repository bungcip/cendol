use super::semantic_common::setup_lowering;
use crate::ast::NameId;

fn check_type(source: &str, expected: &str) {
    let (_ast, registry, symbol_table) = setup_lowering(source);
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(registry.display_qual_type(symbol.type_info), expected);
}

#[test]
fn test_long_unsigned_int() {
    check_type("long unsigned int x;", "unsigned long");
}

#[test]
fn test_unsigned_long_int() {
    check_type("unsigned long int x;", "unsigned long");
}

#[test]
fn test_long_int() {
    check_type("long int x;", "long");
}

#[test]
fn test_short_int() {
    check_type("short int x;", "short");
}

#[test]
fn test_unsigned_short_int() {
    check_type("unsigned short int x;", "unsigned short");
}

#[test]
fn test_long_long_int() {
    check_type("long long int x;", "long long");
}

#[test]
fn test_unsigned_long_long_int() {
    check_type("unsigned long long int x;", "unsigned long long");
}

#[test]
fn test_long_double() {
    check_type("long double x;", "long double");
}

#[test]
fn test_long_const_long() {
    check_type("long const long x;", "const long long");
}

#[test]
fn test_unsigned_long_const_long() {
    check_type("unsigned long const long x;", "const unsigned long long");
}

#[test]
fn test_restrict_array_of_pointers() {
    use crate::tests::test_utils;
    use crate::driver::artifact::CompilePhase;

    let source = r#"
        int main() {
            int x;
            int * restrict arr[10];
            arr[0] = &x;
        }
    "#;
    let (_driver, result) = test_utils::run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok(), "Compilation failed: {:?}", result.err());
}
