//! Tests for switch statement codegen
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::test_utils;

#[test]
fn test_switch_unreachable_cases() {
    let source = r#"
        int printf(const char *, ...);
        int main() {
            int x = 0;
            switch (x) {
                case 1:
                    printf("case_1_marker");
                    break;
                case 2:
                    printf("case_2_marker");
                    break;
                default:
                    printf("default_marker");
                    break;
            }
            return 0;
        }
    "#;

    let clif_ir = setup_cranelift(source);
    insta::assert_snapshot!(test_utils::sort_clif_ir(&clif_ir), @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 4
        ss1 = explicit_slot 1
        ss2 = explicit_slot 1
        gv0 = symbol colocated userextname0
        gv1 = symbol colocated userextname3
        gv2 = symbol colocated userextname4
        sig0 = (i64) -> i32 system_v
        sig1 = (i64) -> i32 system_v
        sig2 = (i64, i64) -> i64, i64 system_v
        sig3 = (i64) -> i32 system_v
        sig4 = (i64) -> i32 system_v
        sig5 = (i64, i64) -> i64, i64 system_v
        sig6 = (i64) -> i32 system_v
        sig7 = (i64) -> i32 system_v
        sig8 = (i64, i64) -> i64, i64 system_v
        fn0 = u0:1 sig0
        fn1 = colocated u0:2 sig2
        fn2 = u0:1 sig3
        fn3 = colocated u0:2 sig5
        fn4 = u0:1 sig6
        fn5 = colocated u0:2 sig8

    block0:
        v0 = iconst.i32 0
        v42 = stack_addr.i64 ss0
        store notrap v0, v42  ; v0 = 0
        v41 = stack_addr.i64 ss0
        v1 = load.i32 notrap v41
        v2 = iconst.i32 1
        v3 = icmp eq v1, v2  ; v2 = 1
        v4 = iconst.i8 1
        v5 = iconst.i8 0
        v6 = select v3, v4, v5  ; v4 = 1, v5 = 0
        v40 = stack_addr.i64 ss1
        store notrap v6, v40
        v39 = stack_addr.i64 ss1
        v7 = load.i8 notrap v39
        v8 = uextend.i32 v7
        brif v8, block2, block5

    block5:
        v38 = stack_addr.i64 ss0
        v9 = load.i32 notrap v38
        v10 = iconst.i32 2
        v11 = icmp eq v9, v10  ; v10 = 2
        v12 = iconst.i8 1
        v13 = iconst.i8 0
        v14 = select v11, v12, v13  ; v12 = 1, v13 = 0
        v37 = stack_addr.i64 ss2
        store notrap v14, v37
        v36 = stack_addr.i64 ss2
        v15 = load.i8 notrap v36
        v16 = uextend.i32 v15
        brif v16, block3, block6

    block6:
        jump block4

    block4:
        v17 = symbol_value.i64 gv0
        v18 = func_addr.i64 fn0
        v19 = iconst.i64 0
        v20, v21 = call fn1(v19, v18)  ; v19 = 0
        v22 = call_indirect sig1, v21(v17)
        jump block1

    block1:
        v23 = iconst.i32 0
        return v23  ; v23 = 0

    block3:
        v24 = symbol_value.i64 gv1
        v25 = func_addr.i64 fn2
        v26 = iconst.i64 0
        v27, v28 = call fn3(v26, v25)  ; v26 = 0
        v29 = call_indirect sig4, v28(v24)
        jump block1

    block2:
        v30 = symbol_value.i64 gv2
        v31 = func_addr.i64 fn4
        v32 = iconst.i64 0
        v33, v34 = call fn5(v32, v31)  ; v32 = 0
        v35 = call_indirect sig7, v34(v30)
        jump block1
    }
    ");
}
