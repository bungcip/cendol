use super::semantic_common::setup_mir;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_array_init_bug_mir() {
    // This reproduces the case from semantic_array_init_bug.rs but checks the MIR
    // instead of just compilation success.
    // Expected: 5 at index 0, 0 at index 1 (implicit), 2 at index 2 (explicit designated), 3 at index 3 (positional after designated)
    let source = r#"
        int a[] = {5, [2] = 2, 3};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [4]%t0

    global @a: [4]i32 = const array_literal [const 5, const zero, const 2, const 3]
    ");
}

#[test]
fn test_array_designator_simple() {
    let source = r#"
        int a[5] = {[1] = 10, [3] = 30};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [5]%t0

    global @a: [5]i32 = const array_literal [const zero, const 10, const zero, const 30, const zero]
    ");
}

#[test]
fn test_array_designator_out_of_order() {
    let source = r#"
        int a[5] = {[3] = 30, [1] = 10};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [5]%t0

    global @a: [5]i32 = const array_literal [const zero, const 10, const zero, const 30, const zero]
    ");
}

#[test]
fn test_array_designator_override() {
    // C11 allows later initializers to override earlier ones
    let source = r#"
        int a[3] = {[1] = 10, [1] = 20};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [3]%t0

    global @a: [3]i32 = const array_literal [const zero, const 20, const zero]
    ");
}

#[test]
fn test_struct_designator_simple() {
    let source = r#"
        struct S { int x; int y; };
        struct S s = {.y = 2, .x = 1};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct S { x: %t1, y: %t1 }
    type %t1 = i32

    global @s: %t0 = const struct_literal { 0: const 1, 1: const 2 }
    ");
}

#[test]
fn test_mixed_array_struct_designators() {
    let source = r#"
        struct S { int arr[3]; int val; };
        struct S s = { .val = 99, .arr = {[1] = 10} };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct S { arr: %t2, val: %t1 }
    type %t1 = i32
    type %t2 = [3]%t1

    global @s: %t0 = const struct_literal { 0: const array_literal [const zero, const 10, const zero], 1: const 99 }
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
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct contains_empty { a: %t1, empty: %t2, b: %t1 }
    type %t1 = u8
    type %t2 = struct anonymous {  }
    type %t3 = i32

    global @ce: %t0 = const struct_literal { 0: const 1, 1: const struct_literal {  }, 2: const 18 }
    global @.L.str0: %t2 = const struct_literal {  }
    ");
}

#[test]
fn test_scalar_braced_init() {
    let source = r#"
        int a = { 1 };
        // int b = { 1, 2 }; // Excess ignored but causes error in Analyzer
        int c = { }; // Zero init (GNU/C23)
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32

    global @a: i32 = const 1
    global @c: i32 = const zero
    ");
}

#[test]
fn test_fam_initialization() {
    let source = r#"
        struct S { int x; int y[]; };
        struct S s = { 1, {2, 3} };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct S { x: %t1, y: %t2 }
    type %t1 = i32
    type %t2 = [0]%t1

    global @s: %t0 = const struct_literal { 0: const 1, 1: const array_literal [const 2, const 3] }
    ");
}

#[test]
fn test_range_designators() {
    let source = r#"
        int a[10] = { [1 ... 3] = 5, [5 ... 6] = 6 };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [10]%t0

    global @a: [10]i32 = const array_literal [const zero, const 5, const 5, const 5, const zero, const 6, const 6, const zero, const zero, const zero]
    ");
}

#[test]
fn test_scalar_to_aggregate_elision() {
    let source = r#"
        struct S { int x; int y; };
        struct Wrapper { struct S s; };
        // Scalar 1 initializes Wrapper.s.x. 0 initializes Wrapper.s.y
        struct Wrapper w = { 1 };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct Wrapper { s: %t1 }
    type %t1 = struct S { x: %t2, y: %t2 }
    type %t2 = i32

    global @w: %t0 = const struct_literal { 0: const struct_literal { 0: const 1 } }
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
    insta::assert_snapshot!(mir, @"
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
    insta::assert_snapshot!(mir, @"
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
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0 }

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{0: const 1, 1: const 2}
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
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = struct S { arr: %t2, val: %t0 }
    type %t2 = [3]%t0

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{0: const array_literal [const zero, const 10, const zero], 1: const 99}
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
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
      }

      bb1:
        %grid = [const array_literal [const 1, const 2], const array_literal [const 3, const 4]]
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
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
      }

      bb1:
        %grid = [const array_literal [const 1, const 2], const array_literal [const 3, const 4]]
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
    insta::assert_snapshot!(mir, @"
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
    let source = r#"
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
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_braced_wide_string_init() {
    let source = r#"
        typedef int wchar_t;
        typedef unsigned short char16_t;
        typedef unsigned int char32_t;

        wchar_t s[] = { L"hello" };
        char16_t s16[] = { u"hi" };
        char32_t s32[] = { U"hey" };

        int main() {
            if (sizeof(s) != 24) return 1; // 6 * 4
            if (sizeof(s16) != 6) return 2; // 3 * 2
            if (sizeof(s32) != 16) return 3; // 4 * 4
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_nested_struct_designator() {
    let source = r#"
        struct SEA { int i; int j; };
        struct SEB { struct SEA a; };
        struct SEB b = { .a.j = 5 };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct SEB { a: %t1 }
    type %t1 = struct SEA { i: %t2, j: %t2 }
    type %t2 = i32

    global @b: %t0 = const struct_literal { 0: const struct_literal { 1: const 5 } }
    ");
}

#[test]
fn test_wide_string_init() {
    let source = r#"
        typedef int wchar_t;
        wchar_t s[] = L"hello";
        int main() {
            if (sizeof(s) != 24) return 1; // 6 * 4
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_string_literal_concatenated_init() {
    let source = r#"
        #define B "b"
        char s[] = "a" B "c";
        int main() {
            if (sizeof(s) != 4) return 1;
            if (s[0] != 'a' || s[1] != 'b' || s[2] != 'c' || s[3] != '\0') return 2;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_array_init_bug() {
    let source = r#"
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
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_struct_array_brace_elision() {
    let source = r#"
        struct S { unsigned char c[2]; };
        struct S gs = {1, 2};
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct S { c: %t2 }
    type %t1 = u8
    type %t2 = [2]%t1
    type %t3 = i32

    global @gs: %t0 = const struct_literal { 0: const array_literal [const 1, const 2] }
    ");
}

#[test]
fn test_brace_elision_designator_break() {
    let source = r#"
        struct Inner { int a; };
        struct Outer { struct Inner i; int b; };
        struct Outer o = { 1, .b = 2 };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = struct Outer { i: %t1, b: %t2 }
    type %t1 = struct Inner { a: %t2 }
    type %t2 = i32

    global @o: %t0 = const struct_literal { 0: const struct_literal { 0: const 1 }, 1: const 2 }
    ");
}

#[test]
fn test_unicode_string_init() {
    let source = r#"
        typedef unsigned short char16_t;
        typedef unsigned int char32_t;

        char16_t s16[] = u"hello";
        char32_t s32[] = U"hello";

        int main() {
            if (sizeof(s16) != 12) return 1; // 6 * 2
            if (sizeof(s32) != 24) return 2; // 6 * 4

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_u8_string_init() {
    let source = r#"
        unsigned char s8[] = u8"hello";

        int main() {
            if (sizeof(s8) != 6) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_compound_literal_array_deduction() {
    let source = r#"
        int main() {
            if (sizeof((char[]){"abc"}) != 4) return 1;
            if (sizeof((int[]){1, 2, 3}) != 12) return 2;
            if (sizeof((int[]){[5]=1}) != 24) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_global_array_init_ptr() {
    let source = r#"
        int g_arr[10] = {10, 20, 30, 40, 50, 60, 70, 80, 90, 100};
        int *g_ptr_arr[3] = { &g_arr[5], &g_arr[0], &g_arr[9] };
        int *g_single_ptr = &g_arr[2];

        int main() {
            if (*g_ptr_arr[0] != 60) return 1;
            if (*g_ptr_arr[1] != 10) return 2;
            if (*g_ptr_arr[2] != 100) return 3;
            if (*g_single_ptr != 30) return 4;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

// Test for designated initializer with struct member from pointer
// This was a bug where .daddr = phdr->daddr would fail with
// "type mismatch: expected unsigned char, found const struct"
#[test]
fn test_designated_initializer_struct_from_ptr() {
    let source = r#"
        struct inner { unsigned char x; };
        struct outer { struct inner daddr; struct inner saddr; };
        struct data { struct inner daddr; struct inner saddr; };
        
        int main() {
            struct data d = { .daddr = {1}, .saddr = {2} };
            struct data *phdr = &d;
            struct outer flow = { .daddr = phdr->daddr, .saddr = phdr->saddr };
            return (flow.daddr.x == 1 && flow.saddr.x == 2) ? 0 : 1;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_array_designator_subobject_completion() {
    // Tests that after a designated initializer finishes initializing a subobject,
    // subsequent non-designated items continue to initialize the rest of the current aggregate.
    let source = r#"
        int main() {
            int i[1][3] = {[0][0 ... 1] = 4, 2};
            if (i[0][0] != 4) return 1;
            if (i[0][1] != 4) return 2;
            if (i[0][2] != 2) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_struct_designator_subobject_completion() {
    // Tests that after a designed structure member is initialized, subsequent non-designated items
    // continue to initialize the structure from the next member.
    let source = r#"
        struct S { int a; int b[2]; };
        
        int main() {
            struct S s[2] = { [0].b[0] = 1, 2, 3 };
            if (s[0].a != 0) return 1;
            if (s[0].b[0] != 1) return 2;
            if (s[0].b[1] != 2) return 3;
            if (s[1].a != 3) return 4;
            if (s[1].b[0] != 0 || s[1].b[1] != 0) return 5;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_fam_brace_elision_initialization() {
    let source = r#"
        struct S { int c; int arr[]; };
        struct S s = {1, 2, 3};
        int main(void) {
            if (sizeof(s) != 4) return 1;
            if (s.c != 1) return 2;
            if (s.arr[0] != 2) return 3;
            if (s.arr[1] != 3) return 4;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_union_init_with_different_types() {
    // Regression test for union initialization bug where members with different types than
    // the first member were incorrectly truncated.
    let source = r#"
        union U {
            int a;
            double b;
            void *c;
        };
        int main() {
            void *p = (void *)0x1234567890ABCDEF;
            union U u = { .c = p };
            if (u.c != p) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_union_init_mir() {
    let source = r#"
        union U {
            int a;
            double b;
            void *c;
        };
        void f(void *p) {
            union U u = { .c = p };
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = void
    type %t1 = ptr<%t0>
    type %t2 = union U { a: %t3, b: %t4, c: %t1 }
    type %t3 = i32
    type %t4 = f64

    fn f(%param0: ptr<void>) -> void
    {
      locals {
        %u: %t2
      }

      bb1:
        %u = struct{2: %param0}
        return
    }
    ");
}

#[test]
fn test_nested_union_init_mir() {
    let source = r#"
        struct S {
            int x;
            union {
                int a;
                double b;
            };
        };
        void f(double d) {
            struct S s = { 1, .b = d };
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = void
    type %t1 = f64
    type %t2 = struct S { x: %t3, a: %t3, b: %t1 }
    type %t3 = i32

    fn f(%param0: f64) -> void
    {
      locals {
        %s: %t2
      }

      bb1:
        %s = struct{0: const 1, 2: %param0}
        return
    }
    ");
}

#[test]
fn test_multidim_array_string_init_designator() {
    let source = r#"
        char arr[][10] = { [0] = "hello" };
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i8
    type %t1 = [10]%t0
    type %t2 = [1]%t1
    type %t3 = [10]%t0

    global @arr: [1][10]i8 = const array_literal [const array_literal [const 104, const 101, const 108, const 108, const 111, const 0, const 0, const 0, const 0, const 0]]
    ");
}

#[test]
fn test_transparent_union_mir() {
    let source = r#"
        typedef union __attribute__((__transparent_union__)) {
            int *i;
            double *d;
        } my_union;
        void f(my_union u);
        void g(int *ip) {
            f(ip);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = void
    type %t1 = i32
    type %t2 = ptr<%t1>
    type %t3 = fn(%t2) -> %t0
    type %t4 = ptr<%t3>

    fn g(%param0: ptr<i32>) -> void
    {

      bb1:
        call f(%param0)
        return
    }

    extern fn f(%param0: ptr<i32>) -> void
    ");
}

#[test]
fn test_typeof_compat_array_size() {
    let source = r#"
        struct tree_entry { int x; };
        struct tree_content {
            int entry_count;
            struct tree_entry *entries[];
        };
        int main() {
            struct tree_content *r = 0;
            struct tree_content *t = 0;
            char arr[1 - 2*!(__builtin_types_compatible_p(__typeof__(*(r->entries)), __typeof__(*(t->entries))))];
            return sizeof(arr);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"
    type %t0 = i32
    type %t1 = struct tree_content { entry_count: %t0, entries: %t4 }
    type %t2 = struct tree_entry { x: %t0 }
    type %t3 = ptr<%t2>
    type %t4 = [0]%t3
    type %t5 = ptr<%t1>
    type %t6 = void
    type %t7 = ptr<%t6>
    type %t8 = i8
    type %t9 = [0]%t8
    type %t10 = u64
    type %t11 = ptr<%t8>

    fn main() -> i32
    {
      locals {
        %r: ptr<%t1>
        %t: ptr<%t1>
        %3: u64
        %4: u64
        %arr: ptr<i8>
        %7: u64
        %8: i32
      }

      bb1:
        %r = const 0
        %t = const 0
        %3 = cast<u64>(const 1) * const 1
        %4 = %3
        %arr = call malloc(%3)
        %7 = cast<u64>(const 1) * const 1
        %8 = cast<i32>(%7)
        call free(cast<ptr<void>>(%arr))
        return %8
    }

    extern fn malloc(%param0: u64) -> ptr<void>

    extern fn free(%param0: ptr<void>) -> void
    ");
}

#[test]
fn test_global_initializer_pointer_to_int_regression() {
    let source = r#"
        int x;
        int y = &x;
    "#;
    run_fail_with_message(source, "initializer element is not computable at load time");
}
