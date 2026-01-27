use crate::tests::semantic_common::setup_mir;

#[test]
fn test_sizeof_logic_not_is_int_size() {
    let src = r#"
    void f() {
        int x;
        unsigned long sz = sizeof(!x);
    }
    "#;
    let mir = setup_mir(src);
    assert!(mir.contains("const 4"), "MIR should contain constant 4 (sizeof int). Dump:\n{}", mir);
    assert!(!mir.contains("const 1"), "MIR should NOT contain constant 1 (sizeof bool). Dump:\n{}", mir);
}

#[test]
fn test_sizeof_logic_and_is_int_size() {
    let src = r#"
    void f() {
        int x;
        unsigned long sz = sizeof(x && x);
    }
    "#;
    let mir = setup_mir(src);
    assert!(mir.contains("const 4"), "MIR should contain constant 4. Dump:\n{}", mir);
    assert!(!mir.contains("const 1"), "MIR should NOT contain constant 1. Dump:\n{}", mir);
}

#[test]
fn test_sizeof_logic_or_is_int_size() {
    let src = r#"
    void f() {
        int x;
        unsigned long sz = sizeof(x || x);
    }
    "#;
    let mir = setup_mir(src);
    assert!(mir.contains("const 4"), "MIR should contain constant 4. Dump:\n{}", mir);
    assert!(!mir.contains("const 1"), "MIR should NOT contain constant 1. Dump:\n{}", mir);
}
