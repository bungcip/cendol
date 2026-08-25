use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_constant_pointer_to_static_duration_object() {
    let src = r#"
        struct Inner { int x; int arr[2]; int *ptr; };
        struct Wrapper { struct Inner *ptr; struct Inner val; };

        static struct Inner s;
        static struct Wrapper w;
        static int arr[1];

        // UnaryOp::AddrOf -> is_static_duration_object
        int *p1 = &(&s)->x;

        // Cast -> is_constant_pointer_to_static_duration_object
        int *p2 = &((struct Inner *)&s)->x;

        // Ident (array) -> is_constant_pointer_to_static_duration_object
        // Ident (function) -> we can declare a function and use it
        void f(void);
        void (*p_func)(void) = &*f;

        // MemberAccess (is_arrow = true)
        int *p4 = &((&w)->ptr)->x;

        // MemberAccess (is_arrow = false)
        int *p5 = &*w.val.arr;

        // UnaryOp::Deref in is_static_duration_object
        int *p6 = &(*&s).x;

        // Global compound literal:
        int *p9 = &(int){1};

        // IndexAccess in is_static_duration_object
        int *p10 = &s.arr[0];
    "#;

    run_pass(src, CompilePhase::SemanticLowering);
}

#[test]
fn test_constant_pointer_fallback() {
    let src = r#"
        // _ => false in is_constant_pointer_to_static_duration_object
        int *p11 = &*(int*)0;

        // Fallback for is_static_duration_object -> `_ => false`
        int *p12 = &1; // Might trigger it, if not parsed as something else.

        // NodeKind::Cast in is_static_duration_object
        // &((int*)0)[0]
        int *p13 = &((int*)0)[0];
    "#;
    run_fail_with_message(src, "Initializer element is not a compile-time constant");
}
