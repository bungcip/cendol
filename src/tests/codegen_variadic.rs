//! Tests for variadic functions
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::{run_c_code_with_output, setup_cranelift};
use crate::tests::test_utils::run_pass;

#[test]
fn test_indirect_variadic_call_validation() {
    run_pass(
        r#"
        int variadic(int count, ...) {
            return count;
        }

        int main() {
            int (*func_ptr)(int, ...) = variadic;
            // Indirect call with extra arguments
            func_ptr(1, 2, 3);
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_extern_variadic_printf_float() {
    let source = r#"
        int printf(const char *fmt, ...);
        int main() {
            printf("%f", 1.0);
            return 0;
        }
    "#;
    let clif_dump = setup_cranelift(source);
    // Ensure the signature matches SystemV ABI (i64, f64) and not the 16-slot padded version.
    // We expect the external function declaration to reflect this.
    assert!(
        clif_dump.contains("(i64, f64) -> i32 system_v"),
        "printf signature mismatch in CLIF:\n{}",
        clif_dump
    );
}

#[test]
fn test_variadic_al_setup() {
    let source = r#"
        int printf(const char *fmt, ...);
        int main() {
            double d = 1.0;
            printf("val: %f\n", d);
            return 0;
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // Check for the helper function signature: (i64, i64) -> i64, i64
    assert!(
        clif_dump.contains("(i64, i64) -> i64, i64 system_v"),
        "Missing or incorrect __cendol_set_al signature in CLIF"
    );

    // Check for the helper call. It should have two results (vX, vY = call fnZ(vA, vB)).
    assert!(clif_dump.contains("= call"), "Missing call to __cendol_set_al");

    // Check for call_indirect which uses the address returned by the helper.
    assert!(
        clif_dump.contains("call_indirect"),
        "Missing call_indirect for variadic printf"
    );

    // Check for FP argument count (v4 = iconst.i64 1 in our case, but let's be more general)
    assert!(clif_dump.contains("iconst.i64 1"), "Missing FP argument count constant");
}

#[test]
fn test_printf_long_double() {
    let code = r#"
int printf(const char *fmt, ...);
int main() {
    printf("%.1f", 34.1);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "34.1");
}

#[test]
fn test_printf_mixed_long_double() {
    let code = r#"
int printf(const char *fmt, ...);
int main() {
    printf("%f %.1f %d", 1.0, 34.1, 42);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.000000 34.1 42");
}

// #[test]
// fn test_myprintf_repro() {
//     // Original reproduction case
//     let code = r#"
// #include <stdarg.h>
// int printf(const char *fmt, ...);

// void myprintf(int count, ...) {
//     va_list ap;
//     va_start(ap, count);
//     for (int i = 0; i < count; i++) {
//         double x = va_arg(ap, double);
//         printf("%.1f ", x);
//     }
//     va_end(ap);
//     printf("\n");
// }

// int main() {
//     myprintf(1, 34.1);
//     return 0;
// }
// "#;
//     let output = run_c_code_with_output(code);
//     assert_eq!(output.trim(), "34.1");
// }

#[test]
fn test_printf_double() {
    let code = r#"
int printf(const char *fmt, ...);
int main() {
    printf("%f", 1.25);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.250000");
}

#[test]
fn test_printf_multiple_doubles() {
    let code = r#"
int printf(const char *fmt, ...);
int main() {
    printf("%f, %f", 1.25, 2.5);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1.250000, 2.500000");
}

#[test]
fn test_printf_mixed_types() {
    let code = r#"
int printf(const char *fmt, ...);
int main() {
    printf("int: %d, double: %f, str: %s", 42, 3.14159, "hello");
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "int: 42, double: 3.141590, str: hello");
}

#[test]
fn test_variadic_limit_hfa() {
    let code = r#"
int printf(const char *fmt, ...);

struct hfa34 { double a, b, c, d; } hfa34 = { 34.1, 34.2, 34.3, 34.4 };

void myprintf(int ignored, ...) {
    __builtin_va_list ap;
    __builtin_va_start(ap, ignored);
    struct hfa34 x1 = __builtin_va_arg(ap, struct hfa34);
    printf("%.1f,%.1f ", x1.a, x1.d);
    struct hfa34 x2 = __builtin_va_arg(ap, struct hfa34);
    printf("%.1f,%.1f ", x2.a, x2.d);
    struct hfa34 x3 = __builtin_va_arg(ap, struct hfa34);
    printf("%.1f,%.1f ", x3.a, x3.d);
    struct hfa34 x4 = __builtin_va_arg(ap, struct hfa34);
    printf("%.1f,%.1f", x4.a, x4.d);
    __builtin_va_end(ap);
}

int main() {
    myprintf(0, hfa34, hfa34, hfa34, hfa34);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "34.1,34.4 34.1,34.4 34.1,34.4 34.1,34.4");
}

#[test]
fn test_builtin_va_copy() {
    let code = r#"
int printf(const char *fmt, ...);

void myprintf(int ignored, ...) {
    __builtin_va_list ap, ap2;
    __builtin_va_start(ap, ignored);
    __builtin_va_copy(ap2, ap);
    int x1 = __builtin_va_arg(ap, int);
    int x2 = __builtin_va_arg(ap2, int);
    printf("%d %d\n", x1, x2);
    __builtin_va_end(ap2);
    __builtin_va_end(ap);
}

int main() {
    myprintf(0, 42);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "42 42");
}
