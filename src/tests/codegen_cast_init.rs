use crate::tests::codegen_common::setup_cranelift;

#[test]
fn test_struct_identity_cast_cranelift_ir() {
    let src = "
        struct S { int a; };
        void foo() {
            struct S s;
            struct S s2 = (struct S)s;
        }
    ";

    let clif_output = setup_cranelift(src);
    insta::assert_snapshot!(clif_output, @"
    ; Function: foo
    function u0:0() system_v {
        ss0 = explicit_slot 4
        ss1 = explicit_slot 4
        sig0 = (i64, i64, i64) -> i64 system_v
        fn0 = u0:1 sig0

    block0:
        v0 = stack_addr.i64 ss0
        v1 = stack_addr.i64 ss1
        v2 = iconst.i64 4
        v3 = call fn0(v1, v0, v2)  ; v2 = 4
        return
    }
    ");
}
