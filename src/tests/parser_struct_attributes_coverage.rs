use crate::tests::parser_utils::setup_translation_unit;

#[test]
fn test_struct_member_attributes() {
    let _ = setup_translation_unit(
        r#"
        struct Outer {
            struct Inner { int x; } __attribute__((packed));
            struct Inner2 { int x; } c __attribute__((packed));
            int d __asm__("foo");
            int e __attribute__((packed)) __attribute__((aligned(8)));
        };
    "#,
    );
}
