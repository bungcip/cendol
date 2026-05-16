use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_alignas_on_bitfield_fails() {
    run_fail_with_message(
        r#"
        struct S {
            _Alignas(16) int x : 5;
        };
        "#,
        "alignment specifier cannot be used in a bit-field",
    );
}

#[test]
fn test_gnu_aligned_on_bitfield_passes() {
    run_pass(
        r#"
        struct S {
            int x : 5 __attribute__((aligned(16)));
        };
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_mixed_alignment_on_bitfield_fails() {
    run_fail_with_message(
        r#"
        struct S {
            _Alignas(16) int x : 5 __attribute__((aligned(16)));
        };
        "#,
        "alignment specifier cannot be used in a bit-field",
    );
}

#[test]
fn test_alignas_alias_on_bitfield_fails() {
    // Standard <stdalign.h> alignas macro (which we simulate here)
    run_fail_with_message(
        r#"
        #define alignas _Alignas
        struct S {
            alignas(16) int x : 5;
        };
        "#,
        "alignment specifier cannot be used in a bit-field",
    );
}

#[test]
fn test_gnu_alignas_alias_on_bitfield_passes() {
    // This matches what contoh.c does
    run_pass(
        r#"
        #define A __attribute__((aligned(16)))
        struct S {
            A int x : 5;
        };
        "#,
        CompilePhase::Mir,
    );
}
