use crate::tests::semantic_common::{find_layout, setup_lowering};

#[test]
fn test_pragma_pack_basic() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(1)
        struct S {
            char a;
            int b;
        };
        "#,
    );

    let layout = find_layout(&registry, "S");
    assert_eq!(layout.size, 5, "Packed struct size should be 5");
    assert_eq!(layout.alignment, 1, "Packed struct alignment should be 1");
}

#[test]
fn test_pragma_pack_push_pop() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(push, 1)
        struct S1 {
            char a;
            int b;
        };
        #pragma pack(pop)
        struct S2 {
            char a;
            int b;
        };
        "#,
    );

    let layout1 = find_layout(&registry, "S1");
    assert_eq!(layout1.size, 5, "S1 size should be 5");

    let layout2 = find_layout(&registry, "S2");
    assert_eq!(layout2.size, 8, "S2 size should be 8 (natural alignment)");
}

#[test]
fn test_pragma_pack_nested() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(1)
        struct S1 {
            char a;
            #pragma pack(2)
            struct S2 {
                char b;
                int c;
            } d;
            int e;
        };
        "#,
    );

    // S2 is defined while pack(2) is active.
    let layout2 = find_layout(&registry, "S2");
    assert_eq!(layout2.size, 6);
    assert_eq!(layout2.alignment, 2);

    // S1 is defined. At the end of S1, pack(2) is still active.
    let layout1 = find_layout(&registry, "S1");
    // a: 0
    // d: alignment 2, offset 2, size 6. (1 -> 2)
    // e: alignment 2 (packed), offset 8, size 4. (2 + 6 = 8)
    // final size 12, alignment 2.
    assert_eq!(layout1.alignment, 2);
    assert_eq!(layout1.size, 12);
}

#[test]
fn test_pragma_pack_empty() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(1)
        struct S1 { char a; int b; };
        #pragma pack()
        struct S2 { char a; int b; };
        "#,
    );
    let layout1 = find_layout(&registry, "S1");
    assert_eq!(layout1.size, 5);
    let layout2 = find_layout(&registry, "S2");
    assert_eq!(layout2.size, 8);
}

#[test]
fn test_pragma_pack_various_values() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(2)
        struct S2 { char a; int b; };
        #pragma pack(4)
        struct S4 { char a; int b; };
        #pragma pack(8)
        struct S8 { char a; int b; };
        "#,
    );

    let l2 = find_layout(&registry, "S2");
    assert_eq!(l2.size, 6);
    assert_eq!(l2.alignment, 2);

    let l4 = find_layout(&registry, "S4");
    assert_eq!(l4.size, 8);
    assert_eq!(l4.alignment, 4);

    let l8 = find_layout(&registry, "S8");
    assert_eq!(l8.size, 8);
    assert_eq!(l8.alignment, 4); // Natural alignment of 'int' is 4, so pack(8) has no effect on it.
}

#[test]
fn test_pragma_pack_alignas_interaction() {
    let (_, registry, _) = setup_lowering(
        r#"
        #pragma pack(1)
        struct S {
            char a;
            _Alignas(4) char b;
        };
        "#,
    );
    let layout = find_layout(&registry, "S");
    // In our implementation, pack caps everything, including _Alignas.
    // member_align = max(natural, alignas).min(pack) = max(1, 4).min(1) = 1.
    assert_eq!(layout.size, 2);
    assert_eq!(layout.alignment, 1);
}

#[test]
fn test_pragma_pack_in_function() {
    let (_, registry, _) = setup_lowering(
        r#"
        void f() {
            #pragma pack(1)
            struct S { char a; int b; };
        }
        "#,
    );
    let layout = find_layout(&registry, "S");
    assert_eq!(layout.size, 5);
}
