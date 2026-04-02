use crate::tests::test_utils::run_fail_with_message;

#[test]
fn rejects_alignas_on_vla() {
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int a[n];
        }
        "#,
        "alignment specifier cannot be used with a variably modified type",
    );
}

#[test]
fn rejects_alignas_on_pointer_to_vla() {
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int (*p)[n];
        }
        "#,
        "alignment specifier cannot be used with a variably modified type",
    );
}

#[test]
fn rejects_alignas_on_function_definition() {
    run_fail_with_message(
        r#"
        _Alignas(16) void f(void) {}
        "#,
        "alignment specifier cannot be used in a function",
    );
}

#[test]
fn rejects_alignas_on_function_declaration() {
    run_fail_with_message(
        r#"
        _Alignas(16) void f(void);
        "#,
        "alignment specifier cannot be used in a function",
    );
}

#[test]
fn rejects_alignas_on_struct_member_vla_pointer() {
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                _Alignas(16) int (*p)[n];
            };
        }
        "#,
        "alignment specifier cannot be used with a variably modified type",
    );
}

#[test]
fn rejects_alignas_on_typedef() {
    run_fail_with_message(
        "typedef _Alignas(16) int aligned_int;",
        "alignment specifier cannot be used in a typedef",
    );
}

#[test]
fn rejects_alignas_on_parameter() {
    run_fail_with_message(
        "void f(_Alignas(16) int x);",
        "alignment specifier cannot be used in a function parameter",
    );
}

#[test]
fn rejects_alignas_on_register_object() {
    run_fail_with_message(
        "void f() { register _Alignas(16) int x; }",
        "alignment specifier cannot be used in a register object",
    );
}

#[test]
fn rejects_alignas_on_bitfield() {
    run_fail_with_message(
        "struct S { _Alignas(16) int x : 1; };",
        "alignment specifier cannot be used in a bit-field",
    );
}
