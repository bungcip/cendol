//! Basic MIR to Cranelift IR lowering tests
use crate::ast::NameId;
use crate::codegen::{ClifGen, ClifOutput, EmitKind};
use crate::driver::artifact::CompilePhase;
use crate::mir::ConstValueKind;
use crate::mir::{MirStmt, MirType, Operand, Place, Rvalue, Terminator};
use crate::tests::codegen_common::{run_c_code_exit_status, setup_cranelift};
use crate::tests::test_utils::run_pass;

#[test]
fn test_boolean_logic_lowering() {
    let source = r#"
            int main() {
                int x;
                x = 4;
                if (!x != 0) return 1;
                if (!!x != 1) return 1;
                return 0;
            }
        "#;
    // Verify it compiles without crashing
    let clif_dump = setup_cranelift(source);
    insta::assert_snapshot!(clif_dump, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 4, align = 4
        ss1 = explicit_slot 4, align = 4
        ss2 = explicit_slot 4, align = 4
        ss3 = explicit_slot 4, align = 4
        ss4 = explicit_slot 4, align = 4
        ss5 = explicit_slot 4, align = 4

    block0:
        v0 = iconst.i32 4
        v60 = stack_addr.i64 ss0
        store notrap v0, v60  ; v0 = 4
        v59 = stack_addr.i64 ss0
        v1 = load.i32 notrap v59
        v2 = iconst.i32 0
        v3 = icmp eq v1, v2  ; v2 = 0
        v4 = iconst.i32 1
        v5 = iconst.i32 0
        v6 = select v3, v4, v5  ; v4 = 1, v5 = 0
        v58 = stack_addr.i64 ss1
        store notrap v6, v58
        v57 = stack_addr.i64 ss1
        v7 = load.i32 notrap v57
        v8 = iconst.i32 0
        v9 = icmp ne v7, v8  ; v8 = 0
        v10 = iconst.i32 1
        v11 = iconst.i32 0
        v12 = select v9, v10, v11  ; v10 = 1, v11 = 0
        v56 = stack_addr.i64 ss2
        store notrap v12, v56
        v55 = stack_addr.i64 ss2
        v13 = load.i32 notrap v55
        v14 = iconst.i32 0
        v15 = icmp ne v13, v14  ; v14 = 0
        v16 = iconst.i8 1
        v17 = iconst.i8 0
        v18 = select v15, v16, v17  ; v16 = 1, v17 = 0
        v19 = uextend.i32 v18
        brif v19, block1, block2

    block2:
        jump block3

    block3:
        v54 = stack_addr.i64 ss0
        v20 = load.i32 notrap v54
        v21 = iconst.i32 0
        v22 = icmp eq v20, v21  ; v21 = 0
        v23 = iconst.i32 1
        v24 = iconst.i32 0
        v25 = select v22, v23, v24  ; v23 = 1, v24 = 0
        v53 = stack_addr.i64 ss3
        store notrap v25, v53
        v52 = stack_addr.i64 ss3
        v26 = load.i32 notrap v52
        v27 = iconst.i32 0
        v28 = icmp eq v26, v27  ; v27 = 0
        v29 = iconst.i32 1
        v30 = iconst.i32 0
        v31 = select v28, v29, v30  ; v29 = 1, v30 = 0
        v51 = stack_addr.i64 ss4
        store notrap v31, v51
        v50 = stack_addr.i64 ss4
        v32 = load.i32 notrap v50
        v33 = iconst.i32 1
        v34 = icmp ne v32, v33  ; v33 = 1
        v35 = iconst.i32 1
        v36 = iconst.i32 0
        v37 = select v34, v35, v36  ; v35 = 1, v36 = 0
        v49 = stack_addr.i64 ss5
        store notrap v37, v49
        v48 = stack_addr.i64 ss5
        v38 = load.i32 notrap v48
        v39 = iconst.i32 0
        v40 = icmp ne v38, v39  ; v39 = 0
        v41 = iconst.i8 1
        v42 = iconst.i8 0
        v43 = select v40, v41, v42  ; v41 = 1, v42 = 0
        v44 = uextend.i32 v43
        brif v44, block4, block5

    block5:
        jump block6

    block6:
        v45 = iconst.i32 0
        return v45  ; v45 = 0

    block4:
        v46 = iconst.i32 1
        return v46  ; v46 = 1

    block1:
        v47 = iconst.i32 1
        return v47  ; v47 = 1
    }
    ");
}

#[test]
fn test_float_to_char_conversion() {
    let source = r#"
            int main() {
                char c = 97.0;
                short s = 98.0;
                return 0;
            }
        "#;
    // Verify it compiles without crashing
    let clif_dump = setup_cranelift(source);
    insta::assert_snapshot!(clif_dump, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 1
        ss1 = explicit_slot 2, align = 2

    block0:
        v0 = f64const 0x1.8400000000000p6
        v1 = fcvt_to_sint_sat.i32 v0  ; v0 = 0x1.8400000000000p6
        v2 = ireduce.i8 v1
        v8 = stack_addr.i64 ss0
        store notrap v2, v8
        v3 = f64const 0x1.8800000000000p6
        v4 = fcvt_to_sint_sat.i32 v3  ; v3 = 0x1.8800000000000p6
        v5 = ireduce.i16 v4
        v7 = stack_addr.i64 ss1
        store notrap v5, v7
        v6 = iconst.i32 0
        return v6  ; v6 = 0
    }
    ");
}

#[test]
fn test_f128_constant_promotion() {
    let mut builder = crate::mir::MirBuilder::new(8);

    // Setup Type F128
    let f128_type_id = builder.add_type(MirType::F128);
    let void_type_id = builder.add_type(MirType::Void);

    // Function
    let func_id = builder.define_function(
        NameId::new("main"),
        vec![],
        void_type_id,
        false,
        crate::mir::MirLinkage::External,
    );

    let const_id = builder.create_constant(f128_type_id, ConstValueKind::Float(34.1));

    {
        let mut fb = builder.build_function(func_id, None);
        let block_id = fb.create_block();
        fb.builder.set_function_entry_block(func_id, block_id);
        fb.set_current_block(block_id);

        // Create a local to hold it
        let local_id = fb.create_local(None, f128_type_id, false);

        // Store it
        fb.add_stmt(MirStmt::Assign(
            Place::Local(local_id),
            Rvalue::Use(Operand::Constant(const_id)),
        ));

        fb.set_terminator(Terminator::Return(None));
    }

    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    match result {
        ClifOutput::ClifDump(clif_ir) => {
            insta::assert_snapshot!(clif_ir, @"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 16, align = 16
                gv0 = symbol colocated userextname0

            block0:
                v0 = symbol_value.i64 gv0
                v1 = load.i64 v0
                v2 = load.i64 v0+8
                v56 = iconst.i64 15
                v3 = ushr v2, v56  ; v56 = 15
                v55 = iconst.i64 1
                v4 = band v3, v55  ; v55 = 1
                v54 = iconst.i64 63
                v5 = ishl v4, v54  ; v54 = 63
                v53 = iconst.i64 0x7fff
                v6 = band v2, v53  ; v53 = 0x7fff
                v52 = iconst.i64 0x7fff
                v7 = icmp eq v6, v52  ; v52 = 0x7fff
                v51 = iconst.i64 -15360
                v8 = iadd v6, v51  ; v51 = -15360
                v9 = iconst.i64 2047
                v10 = select v7, v9, v8  ; v9 = 2047
                v50 = iconst.i64 52
                v11 = ishl v10, v50  ; v50 = 52
                v49 = iconst.i64 0x7fff_ffff_ffff_ffff
                v12 = band v1, v49  ; v49 = 0x7fff_ffff_ffff_ffff
                v48 = iconst.i64 11
                v13 = ushr v12, v48  ; v48 = 11
                v47 = iconst.i64 0x000f_ffff_ffff_ffff
                v14 = band v13, v47  ; v47 = 0x000f_ffff_ffff_ffff
                v15 = bor v5, v11
                v16 = bor v15, v14
                v17 = bitcast.f64 v16
                v18 = stack_addr.i64 ss0
                v19 = iconst.i64 0
                store v19, v18  ; v19 = 0
                store v19, v18+8  ; v19 = 0
                v20 = bitcast.i64 v17
                v46 = iconst.i64 63
                v21 = ushr v20, v46  ; v46 = 63
                v45 = iconst.i64 52
                v22 = ushr v20, v45  ; v45 = 52
                v44 = iconst.i64 2047
                v23 = band v22, v44  ; v44 = 2047
                v43 = iconst.i64 0x000f_ffff_ffff_ffff
                v24 = band v20, v43  ; v43 = 0x000f_ffff_ffff_ffff
                v42 = iconst.i64 2047
                v25 = icmp eq v23, v42  ; v42 = 2047
                v41 = iconst.i64 0x3c00
                v26 = iadd v23, v41  ; v41 = 0x3c00
                v27 = iconst.i64 0x7fff
                v28 = select v25, v27, v26  ; v27 = 0x7fff
                v40 = iconst.i64 15
                v29 = ishl v21, v40  ; v40 = 15
                v30 = bor v29, v28
                v39 = iconst.i64 11
                v31 = ishl v24, v39  ; v39 = 11
                v38 = iconst.i64 0
                v32 = icmp ne v23, v38  ; v38 = 0
                v33 = iconst.i64 -9223372036854775808
                v34 = iconst.i64 0
                v35 = select v32, v33, v34  ; v33 = -9223372036854775808, v34 = 0
                v36 = bor v31, v35
                store v36, v18
                store v30, v18+8
                v37 = iconst.i16 0
                store v37, v18+10  ; v37 = 0
                return
            }
            ");
        }
        ClifOutput::ObjectFile(_) => panic!("Expected Clif dump"),
    }
}

#[test]
fn test_string_literal_pointer_cast_() {
    run_pass(
        r#"
        int strlen(char *);
        int main() {
            char *p;
            p = "hello";
            return 0;
        }
        "#,
        CompilePhase::Cranelift, // NOTE: we test until cranelift to check if validation is correct or not
    );
}

#[test]
fn test_constant_range_validation() {
    run_pass(
        r#"
        int main() {
            unsigned int a = 0xffffffff;
            int b = 0x80010000;
            if (a != 0xffffffff) return 1;
            if (b != 0x80010000) return 2;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_array_with_large_zero_init() {
    // this must be fast
    let source = r#"
        int bigarray[2147483647];
        int main() { return 0; }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}

#[test]
fn test_array_size_in_tenary() {
    let code = r#"
    int main() {
        // This array size calculation relies on constant folding of the ternary operator.
        // If it fails, it might be treated as a VLA of size 0 or cause a crash.
        int a[1 ? 1 : 10];

        a[0] = 42;
        return a[0];
    }
    "#;
    let output = run_c_code_exit_status(code);
    assert_eq!(output, 42);
}

#[test]
fn test_func_ptr_global_comparison() {
    let source = r#"
typedef char *(*readline_t)(const char *);

void* get_ptr() {
    return (void*)0x1234;
}

readline_t l_readline_static = 0;

int main() {
    l_readline_static = (readline_t)((void*)get_ptr());

    // Check if comparison works correctly
    if (l_readline_static != 0) {
        return 0; // Success
    }
    return 1; // Failure
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Function pointer global comparison failed");
}

#[test]
fn test_thread_local_codegen() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            return tls_var;
        }
    "#;
    let clif_ir = setup_cranelift(source);
    insta::assert_snapshot!(clif_ir, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        gv0 = symbol colocated tls userextname0

    block0:
        v0 = tls_value.i64 gv0
        v1 = load.i32 v0
        return v1
    }
    ");
}

#[test]
fn test_thread_local_runtime() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            tls_var += 10;
            return tls_var;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 52);
}

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
        ss0 = explicit_slot 4, align = 4
        ss1 = explicit_slot 4, align = 4
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

#[test]
fn test_store_truncation_overflow_regression() {
    let source = r#"
typedef unsigned char u8;

int main() {
    // Layout: field at 0. padding/sentinel at 1..7.
    // If we increment field, and it stores 4 bytes, it will overwrite 1,2,3.

    struct {
        u8 val;
        u8 pad[7];
    } s;

    // Initialize
    s.val = 10;
    for(int i=0; i<7; i++) s.pad[i] = 0xAA;

    // Increment (s.val++ -> Assign(s.val, Add(s.val, 1)))
    // If store size is not truncated to u8, it writes 4 bytes.
    s.val++;

    if (s.val != 11) return 1;

    for(int i=0; i<3; i++) {
        if (s.pad[i] != 0xAA) {
            return 2;
        }
    }

    return 0;
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Memory corruption detected in store truncation");
}

#[test]
fn test_hex_float_negative_exponent() {
    run_pass(
        r#"
        int main() {
            double d = 0x1.0p-2;
            if (d == 0.25) {
                return 0;
            }
            return 1;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_function_pointer_address_of() {
    let source = r#"
typedef void (*Pfunc)(void);

void runner(Pfunc f) {
    f();
}

void my_func(void) {}

int main() {
    runner(my_func);
    runner(&my_func);
    return 0;
}
"#;
    run_pass(source, CompilePhase::Cranelift);
}
