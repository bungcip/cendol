use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_generic_selection_const_lvalue_prohibited_assignment() {
    // C11 6.5.1.1p5: "The result of a generic selection has the type and value category
    // of the expression in the selected generic association."
    // If the selected expression is a const-qualified lvalue, the _Generic result
    // is also a const-qualified lvalue and cannot be assigned to.
    run_fail_with_message(
        r#"
        int main() {
            int x = 0;
            const int ci = 0;
            _Generic(0, int: ci) = 10;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_generic_selection_const_struct_member_prohibited_assignment() {
    run_fail_with_message(
        r#"
        struct S { const int a; int b; };
        int main() {
            struct S s = {0, 0};
            _Generic(0, int: s.a) = 10;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_generic_selection_const_pointer_deref_prohibited_assignment() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 0;
            const int *p = &x;
            _Generic(0, int: *p) = 10;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}
