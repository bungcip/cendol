use super::semantic_common::setup_mir;

#[test]
fn test_fam_initialization() {
    let source = r#"
        struct S { int x; int y[]; };
        struct S s = { 1, {2, 3} };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_range_designators() {
    let source = r#"
        int a[10] = { [1 ... 3] = 5, [5 ... 6] = 6 };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_scalar_to_aggregate_elision() {
    let source = r#"
        struct S { int x; int y; };
        struct Wrapper { struct S s; };
        // Scalar 1 initializes Wrapper.s.x. 0 initializes Wrapper.s.y
        struct Wrapper w = { 1 };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}
