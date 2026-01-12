use super::semantic_common::setup_lowering;
use crate::ast::NameId;
use crate::semantic::QualType;
use crate::semantic::TypeQualifiers;
use crate::semantic::TypeRegistry;

fn display_qual_type(registry: &TypeRegistry, qt: QualType) -> String {
    let mut s = String::new();
    if qt.is_const() {
        s.push_str("const ");
    }
    if qt.qualifiers().contains(TypeQualifiers::VOLATILE) {
        s.push_str("volatile ");
    }

    let ty_ref = qt.ty();
    let type_cow = registry.get(ty_ref);
    use crate::semantic::TypeKind;
    let kind = &type_cow.kind;

    match kind {
        TypeKind::Pointer { pointee } => {
            let inner = display_qual_type(registry, *pointee);
            s.push_str(&format!("{} *", inner));
        }
        _ => s.push_str(&format!("{}", kind)),
    }
    s.trim().to_string()
}

#[test]
fn test_long_unsigned_int() {
    let (_ast, registry, symbol_table) = setup_lowering("long unsigned int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "unsigned long");
}

#[test]
fn test_unsigned_long_int() {
    let (_ast, registry, symbol_table) = setup_lowering("unsigned long int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "unsigned long");
}

#[test]
fn test_long_int() {
    let (_ast, registry, symbol_table) = setup_lowering("long int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "long");
}

#[test]
fn test_short_int() {
    let (_ast, registry, symbol_table) = setup_lowering("short int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "short");
}

#[test]
fn test_unsigned_short_int() {
    let (_ast, registry, symbol_table) = setup_lowering("unsigned short int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "unsigned short");
}

#[test]
fn test_long_long_int() {
    let (_ast, registry, symbol_table) = setup_lowering("long long int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "long long");
}

#[test]
fn test_unsigned_long_long_int() {
    let (_ast, registry, symbol_table) = setup_lowering("unsigned long long int x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "unsigned long long");
}

#[test]
fn test_long_double() {
    let (_ast, registry, symbol_table) = setup_lowering("long double x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "long double");
}

#[test]
fn test_long_const_long() {
    let (_ast, registry, symbol_table) = setup_lowering("long const long x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(display_qual_type(&registry, symbol.type_info), "const long long");
}

#[test]
fn test_unsigned_long_const_long() {
    let (_ast, registry, symbol_table) = setup_lowering("unsigned long const long x;");
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(
        display_qual_type(&registry, symbol.type_info),
        "const unsigned long long"
    );
}
