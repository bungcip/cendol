use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_auto_type_basic() {
    run_pass(
        r#"
        void test() {
            __auto_type a = 1;
            __auto_type b = 1.0f;
            __auto_type c = 'a';
            __auto_type d = "hello";

            int* pa = &a;
            float* pb = &b;
            int* pc = &c;
            char** pd = &d;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_auto_type_qualifiers() {
    run_pass(
        r#"
        void test() {
            const __auto_type a = 1;
            __auto_type b = a; // b should be int, not const int
            b = 2; // OK

            // a = 2; // Would fail if we checked assignment
        }
        "#,
        CompilePhase::Mir,
    );

    run_fail_with_message(
        r#"
        void test() {
            const __auto_type a = 1;
            a = 2;
        }
        "#,
        "read-only",
    );
}

#[test]
fn test_auto_type_decay() {
    run_pass(
        r#"
        void func() {}
        void test() {
            int arr[10];
            __auto_type p = arr; // deduced as int*
            int* p2 = p;

            __auto_type f = func; // deduced as void(*)()
            f();
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_auto_type_multiple_declarators() {
    run_pass(
        r#"
        void test() {
            __auto_type a = 1, b = 2;
            int* pa = &a;
            int* pb = &b;
        }
        "#,
        CompilePhase::Mir,
    );

    run_fail_with_message(
        r#"
        void test() {
            __auto_type a = 1, b = 1.0;
        }
        "#,
        "deduced as 'int' for one declarator, but 'double' for another",
    );
}

#[test]
fn test_auto_type_no_initializer() {
    run_fail_with_message(
        r#"
        void test() {
            __auto_type a;
        }
        "#,
        "__auto_type requires an initializer",
    );
}

#[test]
fn test_auto_type_initializer_list() {
    run_fail_with_message(
        r#"
        void test() {
            __auto_type a = {1};
        }
        "#,
        "__auto_type is not allowed in initializer list",
    );
}

#[test]
fn test_auto_type_forbidden_contexts() {
    run_fail_with_message(
        r#"
        typedef __auto_type auto_int;
        "#,
        "__auto_type is not allowed in typedef",
    );

    run_fail_with_message(
        r#"
        void func(__auto_type x) {}
        "#,
        "__auto_type is not allowed in function parameter",
    );

    run_fail_with_message(
        r#"
        struct S {
            __auto_type x;
        };
        "#,
        "__auto_type is not allowed in struct or union member",
    );
}

#[test]
fn test_auto_type_complex_declarator() {
    run_fail_with_message(
        r#"
        void test() {
            __auto_type *p = 0;
        }
        "#,
        "__auto_type is not allowed in complex declarator",
    );
}

#[test]
fn test_auto_type_function_return() {
    run_fail_with_message(
        r#"
        __auto_type func() { return 1; }
        "#,
        "__auto_type is not allowed in function return type",
    );
}
