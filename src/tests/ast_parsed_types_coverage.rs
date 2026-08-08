use crate::ast::parsed_types::{PTypeArena, PDeclarator};
use crate::ast::PNodeRef;
use crate::ast::parsed::DeclSpec;

#[test]
fn test_get_declarator_scope_coverage() {
    let mut arena = PTypeArena::default();

    // Identifier declarator is the base
    let base_decl = arena.alloc_decl(PDeclarator::Identifier(None));

    // Add BitField wrapping base
    let bitfield_decl = arena.alloc_decl(PDeclarator::BitField {
        inner: base_decl,
        width: PNodeRef::new(1).unwrap(),
    });

    // Add Attribute wrapping BitField
    let attr_decl = arena.alloc_decl(PDeclarator::Attribute {
        inner: bitfield_decl,
        spec: DeclSpec::Attribute,
    });

    // Traverse through Attribute -> BitField -> Identifier
    assert_eq!(arena.get_declarator_scope(attr_decl), None);
}
