use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::semantic_common::setup_mir;
use crate::tests::test_utils::{run_fail, run_fail_with_message, run_pass};

#[test]
fn test_sizeof_logic_not_is_int_size() {
    let src = r#"
    void f() {
        int x;
        unsigned long sz = sizeof(!x);
    }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = u64

    fn f() -> void
    {
      locals {
        %x: i32
        %sz: u64
      }

      bb1:
        %sz = const 4
        return
    }
    ");
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
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = u64

    fn f() -> void
    {
      locals {
        %x: i32
        %sz: u64
      }

      bb1:
        %sz = const 4
        return
    }
    ");
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
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = u64

    fn f() -> void
    {
      locals {
        %x: i32
        %sz: u64
      }

      bb1:
        %sz = const 4
        return
    }
    ");
}

#[test]
fn test_compound_add_assign() {
    let exit_code = run_c_code_exit_status("int main() { int x = 5; x += 3; return x; }");
    assert_eq!(exit_code, 8, "Expected exit code 8 for x += 3");
}

#[test]
fn test_compound_sub_assign() {
    let exit_code = run_c_code_exit_status("int main() { int x = 5; x -= 3; return x; }");
    assert_eq!(exit_code, 2, "Expected exit code 2 for x -= 3");
}

#[test]
fn test_compound_mul_assign() {
    let exit_code = run_c_code_exit_status("int main() { int x = 5; x *= 3; return x; }");
    assert_eq!(exit_code, 15, "Expected exit code 15 for x *= 3");
}

#[test]
fn test_compound_div_assign() {
    let exit_code = run_c_code_exit_status("int main() { int x = 10; x /= 2; return x; }");
    assert_eq!(exit_code, 5, "Expected exit code 5 for x /= 2");
}

#[test]
fn test_compound_mod_assign() {
    let exit_code = run_c_code_exit_status("int main() { int x = 10; x %= 3; return x; }");
    assert_eq!(exit_code, 1, "Expected exit code 1 for x %= 3");
}

#[test]
fn test_compound_mixed_types() {
    let exit_code = run_c_code_exit_status(
        r#"
        int main() {
            short s = 10;
            long l = 3;
            s -= l;
            return s;
        }
    "#,
    );
    assert_eq!(exit_code, 7, "Expected exit code 7 for short -= long");
}

#[test]
fn test_compound_unsigned_mixed_types() {
    let exit_code = run_c_code_exit_status(
        r#"
        int main() {
            unsigned char c = 5;
            int i = 2;
            c += i;
            return c;
        }
    "#,
    );
    assert_eq!(exit_code, 7, "Expected exit code 7 for unsigned char += int");
}

#[test]
fn test_pointer_add_assign() {
    let code = r#"
int main() {
    int arr[2];
    int *p = &arr[0];
    p += 1;
    if (p == &arr[1]) return 0;
    return 1;
}
"#;
    let result = run_c_code_exit_status(code);
    assert_eq!(result, 0, "Pointer should point to the second element");
}

#[test]
fn test_pointer_sub_assign() {
    let code = r#"
int main() {
    int arr[2];
    int *p = &arr[1];
    p -= 1;
    if (p == &arr[0]) return 0;
    return 1;
}
"#;
    let result = run_c_code_exit_status(code);
    assert_eq!(result, 0, "Pointer should point to the first element");
}

#[test]
fn test_assign_struct_to_int() {
    let source = r#"
        struct A { int x; };
        int main() {
            struct A a;
            int i;
            i = a;
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected int, found struct A");
}

#[test]
fn test_assign_int_to_struct() {
    let source = r#"
        struct A { int x; };
        int main() {
            struct A a;
            a = 10;
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected struct A, found int");
}

#[test]
fn test_assign_incompatible_struct() {
    let source = r#"
        struct A { int x; };
        struct B { int x; };

        int main() {
            struct A a;
            struct B b;
            a = b; 
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected struct A, found struct B");
}

#[test]
fn test_assign_incompatible_pointers() {
    let source = r#"
        int main() {
            int a = 10;
            int *p = &a;
            float *f;
            f = p;
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected float*, found int*");
}

#[test]
fn test_assign_int_to_pointer() {
    let source = r#"
        int main() {
            int *p;
            p = 5; // Invalid (except 0)
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected int*, found int");
}

#[test]
fn test_assign_pointer_to_int() {
    let source = r#"
        int main() {
            int i;
            int *p;
            i = p; // Invalid without cast
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected int, found int*");
}

#[test]
fn test_assign_struct_mismatch() {
    let source = r#"
        struct A { int x; };
        struct B { int x; };
        int main() {
            struct A a;
            struct B b;
            a = b;
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected struct A, found struct B");
}

#[test]
fn test_assign_valid_void_ptr() {
    let source = r#"
        int main() {
            int a;
            int *p = &a;
            void *v;
            v = p; // int* -> void* OK
            p = v; // void* -> int* OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = void
    type %t3 = ptr<%t2>

    fn main() -> i32
    {
      locals {
        %a: i32
        %p: ptr<i32>
        %v: ptr<void>
      }

      bb1:
        %p = addr_of(%a)
        %v = cast<ptr<void>>(%p)
        %p = cast<ptr<i32>>(%v)
        return const 0
    }
    ");
}

#[test]
fn test_assign_valid_null_ptr() {
    let source = r#"
        int main() {
            int *p;
            p = 0; // OK
            p = (void*)0; // OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = void
    type %t3 = ptr<%t2>

    fn main() -> i32
    {
      locals {
        %p: ptr<i32>
      }

      bb1:
        %p = cast<ptr<i32>>(const 0)
        %p = cast<ptr<i32>>(const 0)
        return const 0
    }
    ");
}

#[test]
fn test_assign_pointer_to_bool() {
    let source = r#"
        int main() {
            int *p;
            _Bool b;
            b = p; // OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = bool

    fn main() -> i32
    {
      locals {
        %p: ptr<i32>
        %b: bool
      }

      bb1:
        %b = %p
        return const 0
    }
    ");
}

#[test]
fn test_assign_valid_arithmetic() {
    let source = r#"
        int main() {
            int i;
            float f;
            i = 3.14; // OK (conversion)
            f = 10;   // OK (conversion)
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = f32
    type %t2 = f64

    fn main() -> i32
    {
      locals {
        %i: i32
        %f: f32
      }

      bb1:
        %i = cast<i32>(const 3.14)
        %f = cast<f32>(const 10)
        return const 0
    }
    ");
}

#[test]
fn test_void_init_variable() {
    let source = r#"
        void foo() {}

        int main() {
            int x = foo();
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected int, found void");
}

#[test]
fn test_void_assign_variable() {
    let source = r#"
        void foo() {}

        int main() {
            int x;
            x = foo();
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected int, found void");
}

#[test]
fn test_assign_enum_to_int() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e = X;
            int i = e;
            return i;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
        %i: i32
      }

      bb1:
        %e = const 0
        %i = %e
        return %i
    }
    ");
}

#[test]
fn test_assign_int_to_enum() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e;
            e = 0;
            return e;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
      }

      bb1:
        %e = const 0
        return %e
    }
    ");
}

#[test]
fn test_enum_constant_assignment() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e;
            e = X;
            return e;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
      }

      bb1:
        %e = const 0
        return %e
    }
    ");
}

#[test]
fn test_enum_arithmetic() {
    let source = r#"
        enum E { X = 5 };
        int main() {
            enum E e = X;
            return e + 1;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
        %2: i32
      }

      bb1:
        %e = const 5
        %2 = %e + const 1
        return %2
    }
    ");
}

#[test]
fn test_long_double_arithmetic_conversion() {
    let source = r#"
        int main() {
            long double ld = 1.0;
            float f = 2.0f;
            return (int)(ld + f);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = f80
    type %t2 = f64
    type %t3 = f32

    fn main() -> i32
    {
      locals {
        %ld: f80
        %f: f32
        %3: f80
      }

      bb1:
        %ld = const 1
        %f = const 2
        %3 = %ld fadd cast<f80>(%f)
        return cast<i32>(%3)
    }
    ");
}

// Semantic validation tests for lvalue constraints.

#[test]
fn test_lvalue_assign_to_literal() {
    let source = r#"
        int main() {
            1 = 2;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_assign_to_arithmetic_expr() {
    let source = r#"
        int main() {
            int x;
            x + 1 = 5;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_pre_inc_literal() {
    let source = r#"
        int main() {
            ++1;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_post_inc_literal() {
    let source = r#"
        int main() {
            1++;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_pre_dec_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            --(x + y);
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_post_dec_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            (x + y)--;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_addr_of_rvalue() {
    let source = r#"
        int main() {
            int x;
            &(x + 1);
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}

#[test]
fn test_lvalue_assign_struct_rvalue_member() {
    let source = r#"
        struct S { int x; };
        struct S f() { struct S s; return s; }
        int main() {
            f().x = 1;
        }
    "#;
    run_fail_with_message(source, "Expression is not assignable (not an lvalue)");
}
use crate::tests::test_utils;

#[test]
fn test_sizeof_layout_crash() {
    // This test reproduces a crash where sizeof(T) caused a panic because the layout of T was not computed.
    // The fix ensures that layout is computed for the type operand of sizeof.
    let src = r#"
    int main() {
        int x, *p;

        if (sizeof(0) < 2) return 1;
        if (sizeof 0 < 2) return 1;
        if (sizeof(char) < 1) return 1;
        if (sizeof(int) - 2 < 0) return 1;
        if (sizeof(&x) != sizeof p) return 1;
        return 0;
    }
    "#;

    // Run the pipeline up to MIR generation, which triggers the layout requirement.
    let _ = test_utils::run_pipeline_to_mir(src);
}

#[test]
fn test_static_assert_fail() {
    run_fail("void main() { _Static_assert(0, \"message\"); }", CompilePhase::Mir);
}

#[test]
fn test_static_assert_sizeof() {
    run_pass(
        "void main() { _Static_assert(sizeof(int) == 4, \"size of int is not 4\"); }",
        CompilePhase::Mir,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_long_long_literal_suffix() {
        let source = r#"
            int main() {
                long long a = -2147483648LL;
                long long b = 2147483648LL;
                // Test constant without suffix that fits in unsigned int but not signed int (C11 rules)
                // This is the problematic case for non-suffix literals too
                long long c = 2147483648;
                return 0;
            }
        "#;
        let mir = setup_mir(source);
        insta::assert_snapshot!(mir, @r"
        type %t0 = i32
        type %t1 = i64

        fn main() -> i32
        {
          locals {
            %a: i64
            %b: i64
            %c: i64
          }

          bb1:
            %a = const -2147483648
            %b = const 2147483648
            %c = const 2147483648
            return const 0
        }
        ");
    }
}

#[test]
fn test_nested_const_pointer() {
    let code = "
        const int x = 10;
        const int *p = &x;
        void test() {
            *p = 20;
        }
    ";
    run_fail_with_message(code, "cannot assign to read-only location");
}

#[test]
fn test_const_pointer_to_int() {
    let code = "
        int x = 10;
        int * const p = &x;
        void test() {
            *p = 20; // This should be OK
            p = 0;   // This should fail
        }
    ";
    run_fail_with_message(code, "cannot assign to read-only location");
}

#[test]
fn test_nested_qualifier_preservation() {
    let code = "
        const int x = 10;
        const int * const p = &x;
        void test() {
            *p = 20; // Should fail (pointee is const)
            p = 0;   // Should fail (pointer is const)
        }
    ";
    let driver = run_fail(code, CompilePhase::Mir);
    crate::tests::test_utils::check_diagnostic_message_only(&driver, "cannot assign to read-only location");
    assert_eq!(driver.get_diagnostics().len(), 2);
}

// Comma Operator Tests
#[test]
fn test_comma_operator() {
    let src = r#"
        void test(char *p, char *q) {
            p++, q++;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = i32

    fn test(%param0: ptr<i8>, %param1: ptr<i8>) -> void
    {
      locals {
        %3: ptr<i8>
        %4: ptr<i8>
      }

      bb1:
        %param0 = ptradd(%param0, const 1)
        %3 = %param1
        %4 = ptradd(%param1, const 1)
        %param1 = %4
        return
    }
    ");
}

#[test]
fn test_comma_operator_types() {
    let src = r#"
        void test() {
            int x = 0;
            char *p = 0;
            // (void)x, p  -> type should be char*
            char *q = (x++, p);
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = i8
    type %t3 = ptr<%t2>
    type %t4 = ptr<%t0>

    fn test() -> void
    {
      locals {
        %x: i32
        %p: ptr<i8>
        %q: ptr<i8>
      }

      bb1:
        %x = const 0
        %p = cast<ptr<i8>>(const 0)
        %x = %x + const 1
        %q = %p
        return
    }
    ");
}

#[test]
fn test_comma_operator_loop() {
    let src = r#"
        void loop(char *s, char *f) {
            for (; *f; f++, s++)
                ;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = i32

    fn loop(%param0: ptr<i8>, %param1: ptr<i8>) -> void
    {
      locals {
        %3: ptr<i8>
        %4: ptr<i8>
      }

      bb1:
        br bb2

      bb2:
        cond_br deref(%param1), bb3, bb5

      bb3:
        br bb4

      bb4:
        %param1 = ptradd(%param1, const 1)
        %3 = %param0
        %4 = ptradd(%param0, const 1)
        %param0 = %4
        br bb2

      bb5:
        return
    }
    ");
}

#[test]
fn test_reverse_subscript_with_pointer() {
    let src = r#"
        int main() {
            int a[5][6];
            int (*p)[6];
            p = a;
            int *q;
            q = p[1];
            2[q] = 174;
            return 1[a][2];
        }
    "#;
    run_pass(src, CompilePhase::Mir);
}

// Consolidated from guardian_addr_sizeof_constraints.rs, guardian_pointer_arithmetic.rs, and guardian_type_limits.rs
#[test]
fn test_address_of_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            int *p = &s.x;
            return 0;
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_address_of_register_prohibited() {
    run_fail_with_message(
        r#"
        int main() {
            register int x = 0;
            int *p = &x;
            return 0;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_sizeof_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(s.x);
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );
}

#[test]
fn test_address_of_array_member_identity() {
    run_pass(
        r#"
        struct A
        {
            int k[15];
        };
        int main()
        {
            struct A s;
            int (*p)[15] = &s.k;
            return 35;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_pointer_arithmetic_correctness() {
    use crate::tests::codegen_common::run_c_code_with_output;
    let source = r#"
        int printf(const char* format, ...);
        typedef struct { long a, b, c, d; } MyStruct;
        static const MyStruct arr[] = { {1, 1, 1, 1}, {2, 2, 2, 2} };
        int main() {
            const MyStruct* p_index = &arr[1];
            const MyStruct* p_arith = arr + 1;
            if (p_arith != p_index) return 1;
            printf("PASSED\n");
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert!(output.contains("PASSED"));
}

#[test]
fn test_type_limits_and_token_pasting() {
    let source = r#"
        _Static_assert(__INT_MAX__ == 2147483647, "INT_MAX");
        #define PASTE(x, y) x ## y
        int PASTE(test_, \
var) = 42;
        int main() {
            return test_var - 42;
        }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}
