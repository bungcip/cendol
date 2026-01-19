use super::semantic_common::setup_mir;

#[test]
fn test_array_init_bug_mir() {
    // This reproduces the case from semantic_array_init_bug.rs but checks the MIR
    // instead of just compilation success.
    // Expected: 5 at index 0, 0 at index 1 (implicit), 2 at index 2 (explicit designated), 3 at index 3 (positional after designated)
    let source = r#"
        int a[] = {5, [2] = 2, 3};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_array_designator_simple() {
    let source = r#"
        int a[5] = {[1] = 10, [3] = 30};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_array_designator_out_of_order() {
    let source = r#"
        int a[5] = {[3] = 30, [1] = 10};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_array_designator_override() {
    // C11 allows later initializers to override earlier ones
    let source = r#"
        int a[3] = {[1] = 10, [1] = 20};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_struct_designator_simple() {
    let source = r#"
        struct S { int x; int y; };
        struct S s = {.y = 2, .x = 1};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_mixed_array_struct_designators() {
    let source = r#"
        struct S { int arr[3]; int val; };
        struct S s = { .val = 99, .arr = {[1] = 10} };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}
