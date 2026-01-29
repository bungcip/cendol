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
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [4]%t0

    global @a: [4]i32 = const array_literal [const 5, const zero, const 2, const 3]

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_array_designator_simple() {
    let source = r#"
        int a[5] = {[1] = 10, [3] = 30};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    global @a: [5]i32 = const array_literal [const zero, const 10, const zero, const 30, const zero]

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_array_designator_out_of_order() {
    let source = r#"
        int a[5] = {[3] = 30, [1] = 10};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    global @a: [5]i32 = const array_literal [const zero, const 10, const zero, const 30, const zero]

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_array_designator_override() {
    // C11 allows later initializers to override earlier ones
    let source = r#"
        int a[3] = {[1] = 10, [1] = 20};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [3]%t0

    global @a: [3]i32 = const array_literal [const zero, const 20, const zero]

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_struct_designator_simple() {
    let source = r#"
        struct S { int x; int y; };
        struct S s = {.y = 2, .x = 1};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0 }

    global @s: %t1 = const struct_literal { 1: const 2, 0: const 1 }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_mixed_array_struct_designators() {
    let source = r#"
        struct S { int arr[3]; int val; };
        struct S s = { .val = 99, .arr = {[1] = 10} };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { arr: %t2, val: %t0 }
    type %t2 = [3]%t0

    global @s: %t1 = const struct_literal { 1: const 99, 0: const array_literal [const zero, const 10, const zero] }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_initializer_list_crash_regression() {
    let source = r#"
        typedef unsigned char u8;
        typedef struct {} empty_s;
        struct contains_empty {
            u8 a;
            empty_s empty;
            u8 b;
        };
        struct contains_empty ce = { { (1) }, (empty_s){}, 022, };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct contains_empty { a: %t2, empty: %t3, b: %t2 }
    type %t2 = u8
    type %t3 = struct anonymous {  }

    global @.L.str0: %t3 = const struct_literal {  }
    global @ce: %t1 = const struct_literal { 0: const 1, 1: const struct_literal {  }, 2: const 18 }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_scalar_braced_init() {
    let source = r#"
        int a = { 1 };
        // int b = { 1, 2 }; // Excess ignored but causes error in Analyzer
        int c = { }; // Zero init (GNU/C23)
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    global @a: i32 = const 1
    global @c: i32 = const zero

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}
