use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_typedef_member_function_prohibited() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with ... function type"

    // Test that using a typedef of a function type as a struct member is rejected.
    // In Cendol, this is currently reported at the start of the struct definition
    // because the error is caught during layout computation when the record is completed.
    run_fail_with_diagnostic(
        r#"
typedef void func_t(void);
struct S {
    func_t f;
};
"#,
        CompilePhase::SemanticLowering,
        "member 'f' has function type",
        3,
        1,
    );
}

#[test]
fn test_typedef_member_function_pointer_allowed() {
    // A pointer to a function IS allowed.
    run_pass(
        r#"
typedef void func_t(void);
struct S {
    func_t *f;
};
int main() { return 0; }
"#,
        CompilePhase::Mir,
    );
}
