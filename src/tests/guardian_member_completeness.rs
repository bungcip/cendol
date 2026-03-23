use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_struct_member_constraints() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with... function type
    // or incomplete type."

    // 1. Member with function type
    // In Cendol, this is currently reported at the start of the struct definition
    // due to how spans are propagated in visit_struct_members.
    run_fail_with_diagnostic(
        "struct S { void f(void); };",
        CompilePhase::SemanticLowering,
        "member 'f' has function type",
        1,
        1,
    );

    // 2. Member with incomplete struct type
    run_fail_with_diagnostic(
        "struct Incomplete; struct S { struct Incomplete i; };",
        CompilePhase::SemanticLowering,
        "incomplete type 'struct Incomplete'",
        1,
        20, // Start of struct S
    );

    // 3. Direct recursive definition (detected as recursion)
    run_fail_with_diagnostic(
        "struct S { struct S s; };",
        CompilePhase::SemanticLowering,
        "recursive type definition: struct S",
        1,
        1,
    );
}
