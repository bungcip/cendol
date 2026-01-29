use super::semantic_common::setup_mir;

#[test]
fn test_fam_initialization() {
    let source = r#"
        struct S { int x; int y[]; };
        struct S s = { 1, {2, 3} };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t2 }
    type %t2 = [0]%t0

    global @s: %t1 = const struct_literal { 0: const 1, 1: const array_literal [const 2, const 3] }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_range_designators() {
    let source = r#"
        int a[10] = { [1 ... 3] = 5, [5 ... 6] = 6 };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [10]%t0

    global @a: [10]i32 = const array_literal [const zero, const 5, const 5, const 5, const zero, const 6, const 6, const zero, const zero, const zero]

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
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
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct Wrapper { s: %t2 }
    type %t2 = struct S { x: %t0, y: %t0 }

    global @w: %t1 = const struct_literal { 0: const struct_literal { 0: const 1 } }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}
