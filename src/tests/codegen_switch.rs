//! Tests for switch statement codegen
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::test_utils::{self, run_fail_with_message, run_pass_with_diagnostic_message};

#[test]
fn test_switch_unreachable_cases() {
    let source = r#"
        int main() {
            int x = 0;
            int res = 0;
            switch (x) {
                case 1:
                    res = 11;
                    break;
                case 2:
                    res = 22;
                    break;
                default:
                    res = 33;
                    break;
            }
            return res;
        }
    "#;

    let clif_ir = setup_cranelift(source);
    insta::assert_snapshot!(test_utils::sort_clif_ir(&clif_ir), @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 4, align = 4
        ss1 = explicit_slot 4, align = 4
        ss2 = explicit_slot 1
        ss3 = explicit_slot 1

    block0:
        v0 = iconst.i32 0
        v1 = stack_addr.i64 ss0
        store notrap v0, v1  ; v0 = 0
        v2 = iconst.i32 0
        v3 = stack_addr.i64 ss1
        store notrap v2, v3  ; v2 = 0
        v4 = stack_addr.i64 ss0
        v5 = load.i32 notrap v4
        v6 = iconst.i32 1
        v7 = icmp eq v5, v6  ; v6 = 1
        v8 = iconst.i8 1
        v9 = iconst.i8 0
        v10 = select v7, v8, v9  ; v8 = 1, v9 = 0
        v11 = iconst.i8 0
        v12 = icmp ne v10, v11  ; v11 = 0
        v13 = iconst.i8 1
        v14 = iconst.i8 0
        v15 = select v12, v13, v14  ; v13 = 1, v14 = 0
        v16 = stack_addr.i64 ss2
        store notrap v15, v16
        v17 = stack_addr.i64 ss2
        v18 = load.i8 notrap v17
        v19 = uextend.i32 v18
        brif v19, block2, block5

    block1:
        v20 = stack_addr.i64 ss1
        v21 = load.i32 notrap v20
        return v21

    block2:
        v22 = iconst.i32 11
        v23 = stack_addr.i64 ss1
        store notrap v22, v23  ; v22 = 11
        jump block1

    block3:
        v24 = iconst.i32 22
        v25 = stack_addr.i64 ss1
        store notrap v24, v25  ; v24 = 22
        jump block1

    block4:
        v26 = iconst.i32 33
        v27 = stack_addr.i64 ss1
        store notrap v26, v27  ; v26 = 33
        jump block1

    block5:
        v28 = stack_addr.i64 ss0
        v29 = load.i32 notrap v28
        v30 = iconst.i32 2
        v31 = icmp eq v29, v30  ; v30 = 2
        v32 = iconst.i8 1
        v33 = iconst.i8 0
        v34 = select v31, v32, v33  ; v32 = 1, v33 = 0
        v35 = iconst.i8 0
        v36 = icmp ne v34, v35  ; v35 = 0
        v37 = iconst.i8 1
        v38 = iconst.i8 0
        v39 = select v36, v37, v38  ; v37 = 1, v38 = 0
        v40 = stack_addr.i64 ss3
        store notrap v39, v40
        v41 = stack_addr.i64 ss3
        v42 = load.i8 notrap v41
        v43 = uextend.i32 v42
        brif v43, block3, block6

    block6:
        jump block4
    }
    ");
}

#[test]
fn test_switch_case_overflow() {
    let source = r#"
        int main(void){
            char a = 0;
            switch(a){
                case 0: a = 1;
                break;
                case 256: a = 3;
                break;
                default: a = 5;
                break;
            }
            return a;
        }
    "#;

    // Verify it doesn't crash and produces the warning
    // 256 is in range for promoted type 'int', so it's not a duplicate of '0'.
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "overflow converting case value to switch condition type (256 to 0)",
    );
}

#[test]
fn test_switch_case_duplicate_after_promotion() {
    let source = r#"
        int main(void){
            char a = 0;
            switch(a){
                case 256: a = 1; break;
                case 256: a = 2; break;
            }
            return a;
        }
    "#;

    run_fail_with_message(source, "duplicate case value '256'");
}

#[test]
fn test_implicit_constant_conversion_warning() {
    let source = r#"
        int main() {
            char a = 174;
            return a;
        }
    "#;
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "implicit conversion from 'int' to 'char' changes value from 174 to -82",
    );
}
