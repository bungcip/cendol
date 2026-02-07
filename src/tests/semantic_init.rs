use super::semantic_common::{run_full_pass, setup_mir};

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

#[test]
fn test_local_array_designator_simple() {
    let source = r#"
        int main() {
            int a[5] = {[1] = 10, [3] = 30};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    fn main() -> i32
    {
      locals {
        %a: [5]i32
      }

      bb1:
        %a = [const zero, const 10, const zero, const 30, const zero]
        return const 0
    }
    ");
}

#[test]
fn test_local_array_designator_out_of_order() {
    let source = r#"
        int main() {
            int a[5] = {[3] = 30, [1] = 10};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    fn main() -> i32
    {
      locals {
        %a: [5]i32
      }

      bb1:
        %a = [const zero, const 10, const zero, const 30, const zero]
        return const 0
    }
    ");
}

#[test]
fn test_local_struct_designator_simple() {
    let source = r#"
        struct S { int x; int y; };
        int main() {
            struct S s = {.y = 2, .x = 1};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0 }

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{1: const 2, 0: const 1}
        return const 0
    }
    ");
}

#[test]
fn test_local_mixed_array_struct_designators() {
    let source = r#"
        struct S { int arr[3]; int val; };
        int main() {
            struct S s = { .val = 99, .arr = {[1] = 10} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { arr: %t2, val: %t0 }
    type %t2 = [3]%t0

    fn main() -> i32
    {
      locals {
        %s: %t1
        %2: [3]i32
      }

      bb1:
        %2 = [const zero, const 10, const zero]
        %s = struct{1: const 99, 0: %2}
        return const 0
    }
    ");
}

#[test]
fn test_local_nested_array_init() {
    let source = r#"
        int main() {
            int grid[2][2] = { {1, 2}, {3, 4} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
        %2: [2]i32
        %3: [2]i32
      }

      bb1:
        %2 = [const 1, const 2]
        %3 = [const 3, const 4]
        %grid = [%2, %3]
        return const 0
    }
    ");
}

#[test]
fn test_local_nested_array_init_with_designators() {
    let source = r#"
        int main() {
            int grid[2][2] = { [1] = {[0] = 3, [1] = 4}, [0] = {1, 2} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
        %2: [2]i32
        %3: [2]i32
      }

      bb1:
        %2 = [const 3, const 4]
        %3 = [const 1, const 2]
        %grid = [%3, %2]
        return const 0
    }
    ");
}

#[test]
fn test_local_partial_init_implicit_zero() {
    let source = r#"
        struct S { int x; int y; int z; };
        int main() {
            struct S s = { .y = 5 };
            // x and z should be implicitly zeroed
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0, z: %t0 }

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{1: const 5}
        return const 0
    }
    ");
}

#[test]
fn test_string_literal_array_init() {
    run_full_pass(
        r#"
        char s1[] = "abc";
        char s2[4] = "def";
        const char s3[] = "ghi";
        signed char s4[] = "jkl";
        unsigned char s5[] = "mno";

        int main() {
            if (sizeof(s1) != 4) return 1;
            if (sizeof(s2) != 4) return 2;
            if (sizeof(s3) != 4) return 3;
            if (sizeof(s4) != 4) return 4;
            if (sizeof(s5) != 4) return 5;
            return 0;
        }
    "#,
    );
}

#[test]
fn test_nested_struct_designator() {
    let source = r#"
        struct SEA { int i; int j; };
        struct SEB { struct SEA a; };
        struct SEB b = { .a.j = 5 };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct SEB { a: %t2 }
    type %t2 = struct SEA { i: %t0, j: %t0 }

    global @b: %t1 = const struct_literal { 0: const struct_literal { 1: const 5 } }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_wide_string_init() {
    run_full_pass(
        r#"
        typedef int wchar_t;
        wchar_t s[] = L"hello";
        int main() {
            if (sizeof(s) != 24) return 1; // 6 * 4
            return 0;
        }
    "#,
    );
}

#[test]
fn test_string_literal_concatenated_init() {
    run_full_pass(
        r#"
        #define B "b"
        char s[] = "a" B "c";
        int main() {
            if (sizeof(s) != 4) return 1;
            if (s[0] != 'a' || s[1] != 'b' || s[2] != 'c' || s[3] != '\0') return 2;
            return 0;
        }
    "#,
    );
}

#[test]
fn test_array_init_bug() {
    run_full_pass(
        r#"
        int a[] = {5, [2] = 2, 3};

        int
        main()
        {
            if (sizeof(a) != 4*sizeof(int))
                return 1;

            if (a[0] != 5)
                return 2;
            if (a[1] != 0)
                return 3;
            if (a[2] != 2)
                return 4;
            if (a[3] != 3)
                return 5;

            return 0;
        }
    "#,
    );
}

#[test]
fn test_struct_array_brace_elision() {
    let source = r#"
        struct S { unsigned char c[2]; };
        struct S gs = {1, 2};
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { c: %t3 }
    type %t2 = u8
    type %t3 = [2]%t2

    global @gs: %t1 = const struct_literal { 0: const array_literal [const 1, const 2] }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_brace_elision_designator_break() {
    let source = r#"
        struct Inner { int a; };
        struct Outer { struct Inner i; int b; };
        struct Outer o = { 1, .b = 2 };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct Outer { i: %t2, b: %t0 }
    type %t2 = struct Inner { a: %t0 }

    global @o: %t1 = const struct_literal { 0: const struct_literal { 0: const 1 }, 1: const 2 }

    fn main() -> i32
    {

      bb1:
        return const 0
    }
    ");
}

#[test]
fn test_unicode_string_init() {
    run_full_pass(
        r#"
        typedef unsigned short char16_t;
        typedef unsigned int char32_t;

        char16_t s16[] = u"hello";
        char32_t s32[] = U"hello";

        int main() {
            if (sizeof(s16) != 12) return 1; // 6 * 2
            if (sizeof(s32) != 24) return 2; // 6 * 4

            return 0;
        }
    "#,
    );
}
