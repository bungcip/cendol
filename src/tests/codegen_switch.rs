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
        v43 = stack_addr.i64 ss0
        store notrap v0, v43  ; v0 = 0
        v1 = iconst.i32 0
        v42 = stack_addr.i64 ss1
        store notrap v1, v42  ; v1 = 0
        v41 = stack_addr.i64 ss0
        v2 = load.i32 notrap v41
        v3 = iconst.i32 1
        v4 = icmp eq v2, v3  ; v3 = 1
        v5 = iconst.i8 1
        v6 = iconst.i8 0
        v7 = select v4, v5, v6  ; v5 = 1, v6 = 0
        v8 = iconst.i8 0
        v9 = icmp ne v7, v8  ; v8 = 0
        v10 = iconst.i8 1
        v11 = iconst.i8 0
        v12 = select v9, v10, v11  ; v10 = 1, v11 = 0
        v40 = stack_addr.i64 ss2
        store notrap v12, v40
        v39 = stack_addr.i64 ss2
        v13 = load.i8 notrap v39
        v14 = uextend.i32 v13
        brif v14, block2, block5

    block5:
        v38 = stack_addr.i64 ss0
        v15 = load.i32 notrap v38
        v16 = iconst.i32 2
        v17 = icmp eq v15, v16  ; v16 = 2
        v18 = iconst.i8 1
        v19 = iconst.i8 0
        v20 = select v17, v18, v19  ; v18 = 1, v19 = 0
        v21 = iconst.i8 0
        v22 = icmp ne v20, v21  ; v21 = 0
        v23 = iconst.i8 1
        v24 = iconst.i8 0
        v25 = select v22, v23, v24  ; v23 = 1, v24 = 0
        v37 = stack_addr.i64 ss3
        store notrap v25, v37
        v36 = stack_addr.i64 ss3
        v26 = load.i8 notrap v36
        v27 = uextend.i32 v26
        brif v27, block3, block6

    block6:
        jump block4

    block4:
        v28 = iconst.i32 33
        v35 = stack_addr.i64 ss1
        store notrap v28, v35  ; v28 = 33
        jump block1

    block1:
        v34 = stack_addr.i64 ss1
        v29 = load.i32 notrap v34
        return v29

    block3:
        v30 = iconst.i32 22
        v33 = stack_addr.i64 ss1
        store notrap v30, v33  ; v30 = 22
        jump block1

    block2:
        v31 = iconst.i32 11
        v32 = stack_addr.i64 ss1
        store notrap v31, v32  ; v31 = 11
        jump block1
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
