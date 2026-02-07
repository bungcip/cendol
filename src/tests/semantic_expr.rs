use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::setup_mir;
use crate::tests::test_utils::{run_fail, run_pass, setup_diagnostics_output};
use std::process::Command;
use tempfile::NamedTempFile;

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
        %sz = cast<u64>(const 4)
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
        %sz = cast<u64>(const 4)
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
        %sz = cast<u64>(const 4)
        return
    }
    ");
}
// tests_compound_assign.rs - End-to-end tests for compound assignment operators.
//
// This module contains tests that compile and run C code with compound assignment
// operators to verify their correctness in the generated executable.

fn run_c_code(source: &str) -> i32 {
    let temp_file = NamedTempFile::new().unwrap();
    let temp_path = temp_file.into_temp_path();
    let exe_path = temp_path.to_path_buf();

    let config = crate::driver::cli::CompileConfig {
        input_files: vec![crate::driver::cli::PathOrBuffer::Buffer(
            "test.c".into(),
            source.as_bytes().to_vec(),
        )],
        output_path: Some(exe_path.clone()),
        ..Default::default()
    };

    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let result = driver.run();

    // Check for compilation errors
    if result.is_err() || driver.source_manager.get_file_id("test.c").is_none() {
        driver.print_diagnostics();
        panic!("Compilation failed");
    }

    let run_output = Command::new(exe_path).output().expect("Failed to execute");

    run_output.status.code().unwrap_or(-1)
}

#[test]
fn test_compound_add_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x += 3; return x; }");
    assert_eq!(exit_code, 8, "Expected exit code 8 for x += 3");
}

#[test]
fn test_compound_sub_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x -= 3; return x; }");
    assert_eq!(exit_code, 2, "Expected exit code 2 for x -= 3");
}

#[test]
fn test_compound_mul_assign() {
    let exit_code = run_c_code("int main() { int x = 5; x *= 3; return x; }");
    assert_eq!(exit_code, 15, "Expected exit code 15 for x *= 3");
}

#[test]
fn test_compound_div_assign() {
    let exit_code = run_c_code("int main() { int x = 10; x /= 2; return x; }");
    assert_eq!(exit_code, 5, "Expected exit code 5 for x /= 2");
}

#[test]
fn test_compound_mod_assign() {
    let exit_code = run_c_code("int main() { int x = 10; x %= 3; return x; }");
    assert_eq!(exit_code, 1, "Expected exit code 1 for x %= 3");
}

#[test]
fn test_compound_mixed_types() {
    let exit_code = run_c_code(
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
    let exit_code = run_c_code(
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

fn run_c_code_result(source: &str) -> Result<i32, String> {
    let temp_file = NamedTempFile::new().unwrap();
    let temp_path = temp_file.into_temp_path();
    let exe_path = temp_path.to_path_buf();

    let config = crate::driver::cli::CompileConfig {
        input_files: vec![crate::driver::cli::PathOrBuffer::Buffer(
            "test.c".into(),
            source.as_bytes().to_vec(),
        )],
        output_path: Some(exe_path.clone()),
        ..Default::default()
    };

    let mut driver = crate::driver::compiler::CompilerDriver::from_config(config);
    let result = driver.run();

    if result.is_err() {
        return Err("Compilation failed".into());
    }

    let run_output = Command::new(exe_path).output().expect("Failed to execute");
    Ok(run_output.status.code().unwrap_or(-1))
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
    let result = run_c_code_result(code);
    assert!(result.is_ok(), "Pointer add-assign should compile and run");
    assert_eq!(result.unwrap(), 0, "Pointer should point to the second element");
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
    let result = run_c_code_result(code);
    assert!(result.is_ok(), "Pointer sub-assign should compile and run");
    assert_eq!(result.unwrap(), 0, "Pointer should point to the first element");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found struct A
    Span: SourceSpan(source_id=SourceId(2), start=106, end=111)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found int
    Span: SourceSpan(source_id=SourceId(2), start=87, end=93)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Span: SourceSpan(source_id=SourceId(2), start=141, end=146)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found <pointer>
    Span: SourceSpan(source_id=SourceId(2), start=105, end=110)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found int
    Span: SourceSpan(source_id=SourceId(2), start=54, end=59)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found <pointer>
    Span: SourceSpan(source_id=SourceId(2), start=73, end=78)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Span: SourceSpan(source_id=SourceId(2), start=140, end=145)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Span: SourceSpan(source_id=SourceId(2), start=65, end=70)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Span: SourceSpan(source_id=SourceId(2), start=76, end=85)
    ");
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
// Semantic validation tests for lvalue constraints.

#[test]
fn test_lvalue_assign_to_literal() {
    let source = r#"
        int main() {
            1 = 2;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=34, end=39)
    ");
}

#[test]
fn test_lvalue_assign_to_arithmetic_expr() {
    let source = r#"
        int main() {
            int x;
            x + 1 = 5;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=53, end=62)
    ");
}

#[test]
fn test_lvalue_pre_inc_literal() {
    let source = r#"
        int main() {
            ++1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=34, end=37)
    ");
}

#[test]
fn test_lvalue_post_inc_literal() {
    let source = r#"
        int main() {
            1++;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=34, end=37)
    ");
}

#[test]
fn test_lvalue_pre_dec_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            --(x + y);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=56, end=64)
    ");
}

#[test]
fn test_lvalue_post_dec_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            (x + y)--;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=57, end=65)
    ");
}

#[test]
fn test_lvalue_addr_of_rvalue() {
    let source = r#"
        int main() {
            int x;
            &(x + 1);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=53, end=60)
    ");
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Span: SourceSpan(source_id=SourceId(2), start=110, end=119)
    ");
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
    let output = setup_diagnostics_output(code);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Span: SourceSpan(source_id=SourceId(2), start=88, end=95)
    ");
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
    let output = setup_diagnostics_output(code);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Span: SourceSpan(source_id=SourceId(2), start=125, end=130)
    ");
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
    let output = setup_diagnostics_output(code);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: cannot assign to read-only location
    Span: SourceSpan(source_id=SourceId(2), start=95, end=102)

    Level: Error
    Message: cannot assign to read-only location
    Span: SourceSpan(source_id=SourceId(2), start=150, end=155)
    ");
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
        %5: ptr<i8>
        %6: ptr<i8>
      }

      bb1:
        %3 = %param0
        %4 = ptradd(%param0, const 1)
        %param0 = %4
        %5 = %param1
        %6 = ptradd(%param1, const 1)
        %param1 = %6
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
        %4: i32
        %5: i32
      }

      bb1:
        %x = const 0
        %p = cast<ptr<i8>>(const 0)
        %4 = %x
        %5 = %x + const 1
        %x = %5
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
        %5: ptr<i8>
        %6: ptr<i8>
      }

      bb1:
        br bb2

      bb2:
        cond_br deref(%param1), bb3, bb5

      bb3:
        br bb4

      bb4:
        %3 = %param1
        %4 = ptradd(%param1, const 1)
        %param1 = %4
        %5 = %param0
        %6 = ptradd(%param0, const 1)
        %param0 = %6
        br bb2

      bb5:
        return
    }
    ");
}
