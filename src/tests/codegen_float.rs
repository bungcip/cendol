use crate::{
    ast::NameId,
    codegen::{ClifGen, ClifOutput, EmitKind},
    driver::artifact::CompilePhase,
    mir::{ConstValueKind, MirStmt, MirType, Operand, Place, Rvalue, Terminator},
    tests::{
        codegen_common::{run_c_code_exit_status, setup_cranelift},
        test_utils::run_pass,
    },
};

#[test]
fn test_float_to_bool_cast_nan() {
    let source = r#"
        int main() {
            _Bool b = (_Bool)(0.0/0.0);
            return b;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_ternary_nan() {
    let source = r#"
        int main() {
            return (0.0/0.0) ? 1 : 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_if_nan() {
    let source = r#"
        int main() {
            if (0.0/0.0) {
                return 1;
            } else {
                return 0;
            }
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_while_nan() {
    let source = r#"
        int main() {
            int i = 0;
            while (0.0/0.0) {
                i++;
                if (i >= 1) break;
            }
            return i;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_zero() {
    let source = r#"
        int main() {
            return 0.0 ? 1 : 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn float_to_int_out_of_bounds() {
    run_pass(
        "
        int printf(const char *format, ...);
        int main() {
            // These conversions cause undefined behavior in C11 6.3.1.4p1
            // because the floating-point value cannot be represented in the integer type.
            // However, the compiler should not emit trapping instructions (like ud2 on x64)
            // that crash the program, but instead provide a fallback behavior (e.g. saturation or indefinite value),
            // which is expected by some real-world programs like Lua.

            double d1 = 1e20;
            long long l1 = (long long)d1;

            double d2 = -1e20;
            long long l2 = (long long)d2;

            double d3 = 1.0 / 0.0; // Infinity
            long long l3 = (long long)d3;

            double d4 = 0.0 / 0.0; // NaN
            long long l4 = (long long)d4;

            printf(\"%lld %lld %lld %lld\\n\", l1, l2, l3, l4);
            return 0;
        }
        ",
        CompilePhase::EmitObject,
    );
}

#[test]
fn test_negative_float_to_int_cast_regression() {
    let source = r#"
        int main() {
            double val = -1.0;
            int res = (int)val;
            if (res == -1) {
                return 42;
            }
            return 0;
        }
    "#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 42);
}

#[test]
fn test_negative_float_to_int_implicit_cast_regression() {
    let source = r#"
        int main() {
            double val = -123.456;
            int res;
            res = val; 
            if (res == -123) {
                return 42;
            }
            return 0;
        }
    "#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 42);
}

#[test]
fn test_unreachable_float_return() {
    let source = r#"
        double foo(void) {
        }
        int main() {
            return 0;
        }
    "#;

    let clif_dump = setup_cranelift(source);
    // Should compile without verifier panicking due to `iconst.f64`
    insta::assert_snapshot!(clif_dump, @"
    ; Function: foo
    function u0:0() -> f64 system_v {
    block0:
        v0 = f64const 0.0
        return v0  ; v0 = 0.0
    }


    ; Function: main
    function u0:0() -> i32 system_v {
    block0:
        v0 = iconst.i32 0
        return v0  ; v0 = 0
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
        fb.current_block = Some(block_id);

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
                v3 = iconst.i64 15
                v4 = ushr v2, v3  ; v3 = 15
                v5 = iconst.i64 1
                v6 = band v4, v5  ; v5 = 1
                v7 = iconst.i64 63
                v8 = ishl v6, v7  ; v7 = 63
                v9 = iconst.i64 0x7fff
                v10 = band v2, v9  ; v9 = 0x7fff
                v11 = iconst.i64 0x7fff
                v12 = icmp eq v10, v11  ; v11 = 0x7fff
                v13 = iconst.i64 -15360
                v14 = iadd v10, v13  ; v13 = -15360
                v15 = iconst.i64 2047
                v16 = select v12, v15, v14  ; v15 = 2047
                v17 = iconst.i64 52
                v18 = ishl v16, v17  ; v17 = 52
                v19 = iconst.i64 0x7fff_ffff_ffff_ffff
                v20 = band v1, v19  ; v19 = 0x7fff_ffff_ffff_ffff
                v21 = iconst.i64 11
                v22 = ushr v20, v21  ; v21 = 11
                v23 = iconst.i64 0x000f_ffff_ffff_ffff
                v24 = band v22, v23  ; v23 = 0x000f_ffff_ffff_ffff
                v25 = bor v8, v18
                v26 = bor v25, v24
                v27 = bitcast.f64 v26
                v28 = stack_addr.i64 ss0
                v29 = iconst.i64 0
                store v29, v28  ; v29 = 0
                store v29, v28+8  ; v29 = 0
                v30 = bitcast.i64 v27
                v31 = iconst.i64 63
                v32 = ushr v30, v31  ; v31 = 63
                v33 = iconst.i64 52
                v34 = ushr v30, v33  ; v33 = 52
                v35 = iconst.i64 2047
                v36 = band v34, v35  ; v35 = 2047
                v37 = iconst.i64 0x000f_ffff_ffff_ffff
                v38 = band v30, v37  ; v37 = 0x000f_ffff_ffff_ffff
                v39 = iconst.i64 2047
                v40 = icmp eq v36, v39  ; v39 = 2047
                v41 = iconst.i64 0x3c00
                v42 = iadd v36, v41  ; v41 = 0x3c00
                v43 = iconst.i64 0x7fff
                v44 = select v40, v43, v42  ; v43 = 0x7fff
                v45 = iconst.i64 15
                v46 = ishl v32, v45  ; v45 = 15
                v47 = bor v46, v44
                v48 = iconst.i64 11
                v49 = ishl v38, v48  ; v48 = 11
                v50 = iconst.i64 0
                v51 = icmp ne v36, v50  ; v50 = 0
                v52 = iconst.i64 -9223372036854775808
                v53 = iconst.i64 0
                v54 = select v51, v52, v53  ; v52 = -9223372036854775808, v53 = 0
                v55 = bor v49, v54
                store v55, v28
                store v47, v28+8
                v56 = iconst.i16 0
                store v56, v28+10  ; v56 = 0
                return
            }
            ");
        }
        ClifOutput::ObjectFile(_) => panic!("Expected Clif dump"),
    }
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
