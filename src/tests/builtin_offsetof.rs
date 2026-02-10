use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_builtin_offsetof_simple() {
    let source = r#"
        struct S {
            char a;
            int b;
            char c;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d %d", (int)__builtin_offsetof(struct S, a),
                               (int)__builtin_offsetof(struct S, b),
                               (int)__builtin_offsetof(struct S, c));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // On x86_64: char a (0), padding (1-3), int b (4), char c (8)
    assert_eq!(output, "0 4 8");
}

#[test]
fn test_builtin_offsetof_nested() {
    let source = r#"
        struct Inner {
            char x;
            int y;
        };
        struct Outer {
            char a;
            struct Inner b;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct Outer, b.x),
                             (int)__builtin_offsetof(struct Outer, b.y));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // Outer: char a (0), padding (1-3), Inner b (4)
    // Inner: char x (0), padding (1-3), int y (4)
    // b.x is at 4 + 0 = 4
    // b.y is at 4 + 4 = 8
    assert_eq!(output, "4 8");
}

#[test]
fn test_builtin_offsetof_array() {
    let source = r#"
        struct S {
            int a[10];
            int b;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct S, a[0]),
                             (int)__builtin_offsetof(struct S, a[5]));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "0 20");
}

#[test]
fn test_builtin_offsetof_anonymous() {
    let source = r#"
        struct S {
            char a;
            struct {
                char b;
                int c;
            };
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct S, b),
                             (int)__builtin_offsetof(struct S, c));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // S: char a (0), anonymous struct (starts at 4 due to int c alignment)
    // anonymous: char b (0), int c (4)
    // b is at 4 + 0 = 4
    // c is at 4 + 4 = 8
    assert_eq!(output, "4 8");
}

#[test]
fn test_builtin_offsetof_stddef() {
    let source = r#"
        #include <stddef.h>
        struct S { int a; int b; };
        int printf(const char *, ...);
        int main() {
            printf("%d", (int)offsetof(struct S, b));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "4");
}

#[test]
fn test_builtin_offsetof_constant_context() {
    let source = r#"
        struct S { char a; int b; };
        int main() {
            int arr[__builtin_offsetof(struct S, b)];
            return sizeof(arr) / sizeof(int);
        }
    "#;
    use crate::tests::codegen_common::run_c_code_exit_status;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 4);
}
