use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_bitfield_zero_width_unnamed() {
    // C11 6.7.2.1p12: "As a special case, a bit-field structure member with a width of 0
    // indicates that no further bit-field is to be packed into the unit..."
    // "An unnamed bit-field with a width of 0 shall not specify a declarator..."

    // This should pass
    run_pass(
        r#"struct S { int x : 1; int : 0; int y : 1; };"#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_bitfield_width_exceeds_type() {
    // C11 6.7.2.1p4: "... does not exceed the width of an object of the type..."
    run_fail_with_message(
        r#"struct S { char c : 9; };"#,
        CompilePhase::Mir,
        "width of bit-field (9 bits) exceeds width of its type (8 bits)",
    );
}

#[test]
fn test_named_bitfield_zero_width() {
    // C11 6.7.2.1p12: "An unnamed bit-field with a width of 0 shall not specify a declarator..."
    run_fail_with_message(
        r#"struct S { int x : 0; };"#,
        CompilePhase::Mir,
        "zero-width bit-field shall not specify a declarator",
    );
}
