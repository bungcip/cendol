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
        ss0 = explicit_slot 4, align = 4
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
        v52 = stack_addr.i64 ss0
        store notrap v0, v52  ; v0 = 0
        v51 = stack_addr.i64 ss0
        v1 = load.i32 notrap v51
        v2 = iconst.i32 1
        v3 = icmp eq v1, v2  ; v2 = 1
        v4 = iconst.i8 1
        v5 = iconst.i8 0
        v6 = select v3, v4, v5  ; v4 = 1, v5 = 0
        v7 = iconst.i8 0
        v8 = icmp ne v6, v7  ; v7 = 0
        v9 = iconst.i8 1
        v10 = iconst.i8 0
        v11 = select v8, v9, v10  ; v9 = 1, v10 = 0
        v50 = stack_addr.i64 ss1
        store notrap v11, v50
        v49 = stack_addr.i64 ss1
        v12 = load.i8 notrap v49
        v13 = uextend.i32 v12
        brif v13, block2, block5

    block5:
        v48 = stack_addr.i64 ss0
        v14 = load.i32 notrap v48
        v15 = iconst.i32 2
        v16 = icmp eq v14, v15  ; v15 = 2
        v17 = iconst.i8 1
        v18 = iconst.i8 0
        v19 = select v16, v17, v18  ; v17 = 1, v18 = 0
        v20 = iconst.i8 0
        v21 = icmp ne v19, v20  ; v20 = 0
        v22 = iconst.i8 1
        v23 = iconst.i8 0
        v24 = select v21, v22, v23  ; v22 = 1, v23 = 0
        v47 = stack_addr.i64 ss2
        store notrap v24, v47
        v46 = stack_addr.i64 ss2
        v25 = load.i8 notrap v46
        v26 = uextend.i32 v25
        brif v26, block3, block6

    block6:
        jump block4

    block4:
        v27 = symbol_value.i64 gv0
        v28 = func_addr.i64 fn0
        v29 = iconst.i64 0
        v30, v31 = call fn1(v29, v28)  ; v29 = 0
        v32 = call_indirect sig1, v31(v27)
        jump block1

    block1:
        v33 = iconst.i32 0
        return v33  ; v33 = 0

    block3:
        v34 = symbol_value.i64 gv1
        v35 = func_addr.i64 fn2
        v36 = iconst.i64 0
        v37, v38 = call fn3(v36, v35)  ; v36 = 0
        v39 = call_indirect sig4, v38(v34)
        jump block1

    block2:
        v40 = symbol_value.i64 gv2
        v41 = func_addr.i64 fn4
        v42 = iconst.i64 0
        v43, v44 = call fn5(v42, v41)  ; v42 = 0
        v45 = call_indirect sig7, v44(v40)
        jump block1
    }
    ");
}

#[test]
fn test_switch_case_overflow_regression() {
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
    let (driver, result) = test_utils::run_pipeline(source, crate::driver::artifact::CompilePhase::Mir);
    assert!(
        result.is_ok(),
        "Compilation should have succeeded even with 'case 256' when switch is on 'char'"
    );
    test_utils::check_diagnostic_message_only(
        &driver,
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

    // Should still fail due to actual duplicate in 'int'
    let (driver, result) = test_utils::run_pipeline(source, crate::driver::artifact::CompilePhase::Mir);
    assert!(result.is_err(), "Compilation should fail due to duplicate case 256");
    test_utils::check_diagnostic_message_only(&driver, "duplicate case value '256'");
}

#[test]
fn test_implicit_constant_conversion_warning() {
    let source = r#"
        int main() {
            char a = 174;
            return a;
        }
    "#;
    let (driver, result) = test_utils::run_pipeline(source, crate::driver::artifact::CompilePhase::Mir);
    assert!(result.is_ok(), "Compilation should have succeeded");
    test_utils::check_diagnostic_message_only(
        &driver,
        "implicit conversion from 'int' to 'char' changes value from 174 to -82",
    );
}

#[test]
fn test_switch_case_duplicate_after_truncation() {
    let source = r#"
        int main(void) {
            char a = 0;
            switch(a) {
                case 0: break;
                case 256: break;
            }
            return 0;
        }
    "#;
    // Matching Clang behavior: 256 is NOT a duplicate of 0 because of integer promotion to int.
    // It's allowed with a warning.
    let (driver, result) = test_utils::run_pipeline(source, crate::driver::artifact::CompilePhase::Mir);
    assert!(result.is_ok(), "Compilation should succeed as per Clang behavior");
    test_utils::check_diagnostic_message_only(
        &driver,
        "overflow converting case value to switch condition type (256 to 0)",
    );
}
