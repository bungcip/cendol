use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_fail_with_message};

#[test]
fn rejects_restrict_on_non_pointers() {
    let cases = [
        "int restrict x;",
        "float restrict x;",
        "void (* restrict f)(void);",
    ];

    for c_code in cases {
        run_fail_with_message(c_code, "restrict requires a pointer type");
    }
}

#[test]
fn rejects_restrict_on_arrays() {
    // restrict applied via typedef to an array type
    run_fail_with_message("typedef int A[10]; A restrict x;", "restrict requires a pointer type");
}

#[test]
fn allows_restrict_on_object_pointers() {
    let c_code = r#"
        int * restrict p1;
        void * restrict p2;
        struct S { int a; } * restrict p3;
    "#;
    run_pass(c_code, CompilePhase::SemanticLowering);
}
