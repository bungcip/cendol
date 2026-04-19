use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_pointer_addition_incomplete_struct_prohibited() {
    // C11 6.5.6p2: "one operand shall be a pointer to a complete object type..."
    run_fail_with_message("struct S; void f(struct S *p) { (void)(p + 1); }", "Invalid operands");
}

#[test]
fn test_pointer_addition_function_type_prohibited() {
    // C11 6.5.6p2: Pointer addition requires a pointer to a complete object type.
    // A function type is not an object type.
    run_fail_with_message("void f(void); void g() { (void)(&f + 1); }", "Invalid operands");
}

#[test]
fn test_pointer_subtraction_incomplete_struct_prohibited() {
    // C11 6.5.6p2: "one operand shall be a pointer to a complete object type..."
    run_fail_with_message("struct S; void f(struct S *p) { (void)(p - 1); }", "Invalid operands");
}

#[test]
fn test_pointer_difference_function_type_prohibited() {
    // C11 6.5.6p3: "both operands shall be pointers to qualified or unqualified versions of compatible complete object types"
    run_fail_with_message("void f(void); void g() { (void)(&f - &f); }", "Invalid operands");
}

#[test]
fn test_pointer_addition_void_prohibited() {
    // void is an incomplete type.
    run_fail_with_message("void f(void *p) { (void)(p + 1); }", "Invalid operands");
}

#[test]
fn test_pointer_addition_complete_struct_allowed() {
    run_pass(
        "struct S { int x; }; void f(struct S *p) { (void)(p + 1); }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_pointers_relational_prohibited() {
    // C11 6.5.8p2: Relational operators require pointers to compatible object types.
    // Function pointers are NOT pointers to object types.
    run_fail_with_message(
        r#"
        void f(void);
        void g(void);
        int test() {
            return &f < &g;
        }
        "#,
        "Invalid operands",
    );
}

#[test]
fn test_function_pointers_equality_allowed() {
    // C11 6.5.9p2: Equality operators allow pointers to compatible types (including function types).
    run_pass(
        r#"
        void f(void);
        void g(void);
        int test() {
            return &f == &g;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_relational_void_pointers_allowed() {
    // void is an incomplete object type, so void* is a pointer to an object type.
    run_pass(
        r#"
        int test(void *p, void *q) {
            return p < q;
        }
        "#,
        CompilePhase::Mir,
    );
}
