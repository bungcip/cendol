//! Basic MIR to Cranelift IR lowering tests
use crate::ast::NameId;
use crate::codegen::clif_gen::{EmitContext, emit_const};
use crate::codegen::{ClifGen, ClifOutput, EmitKind};
use crate::driver::artifact::CompilePhase;
use crate::mir::{ConstValueKind, Rvalue};
use crate::mir::{MirModuleId, MirRecordLayout, MirStmt, MirType, Operand, Place, Terminator};
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::test_utils::run_pass;

#[test]
fn test_emit_const_struct_literal() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // 1. Setup Types
    let int_type_id = builder.add_type(MirType::I32);

    let struct_type = MirType::Record {
        name: NameId::new("ValidationTestStruct"),
        field_types: vec![int_type_id, int_type_id],
        field_names: vec![NameId::new("a"), NameId::new("b")],
        is_union: false,
        layout: MirRecordLayout {
            size: 8,
            alignment: 4,
            field_offsets: vec![0, 4],
        },
    };
    let struct_type_id = builder.add_type(struct_type.clone());

    // 2. Setup Constants
    let const_1_id = builder.create_constant(int_type_id, ConstValueKind::Int(0x11111111));
    let const_2_id = builder.create_constant(int_type_id, ConstValueKind::Int(0x22222222));

    let struct_const_kind = ConstValueKind::StructLiteral(vec![(0, const_1_id), (1, const_2_id)]);
    let struct_const_id = builder.create_constant(struct_type_id, struct_const_kind);

    // 3. Get MirProgram
    let mir = builder.consume();

    // 4. Emit Constant
    let mut output = Vec::new();
    let ctx = EmitContext {
        mir: &mir,
        func_id_map: &hashbrown::HashMap::new(),
        data_id_map: &hashbrown::HashMap::new(),
    };
    emit_const(struct_const_id, &mut output, &ctx, None, None, 0).expect("emit_const failed");

    // 5. Verify Output
    insta::assert_yaml_snapshot!(output, @"
    - 17
    - 17
    - 17
    - 17
    - 34
    - 34
    - 34
    - 34
    ");
}

#[test]
fn test_store_statement_lowering() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // 1. Set up Types
    let int_type_id = builder.add_type(MirType::I32);
    let void_type_id = builder.add_type(MirType::Void);

    // 2. Set up Function and Block
    let func_id = builder.define_function(
        NameId::new("main"),
        vec![],
        void_type_id,
        false,
        crate::mir::MirLinkage::Export,
    );
    builder.set_current_function(func_id);

    let entry_block_id = builder.create_block();
    builder.set_current_block(entry_block_id);
    builder.set_function_entry_block(func_id, entry_block_id);

    // 3. Set up Local
    let local_id = builder.create_local(Some(NameId::new("x")), int_type_id, false);

    // 4. Set up Constant
    let const_val_id = builder.create_constant(int_type_id, ConstValueKind::Int(42));

    // 5. Create Statement: store 42 into x
    let store_stmt = MirStmt::Store(Operand::Constant(const_val_id), Place::Local(local_id));
    builder.add_statement(store_stmt);

    builder.set_terminator(Terminator::Return(None));

    // 6. Compile
    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    // 7. Assert
    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            insta::assert_snapshot!(clif_ir, @"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 4

            block0:
                v0 = iconst.i32 42
                v1 = stack_addr.i64 ss0
                store notrap v0, v1  ; v0 = 42
                return
            }
            ");
        }
        Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump, got object file"),
        Err(e) => panic!("MIR to Cranelift lowering failed: {}", e),
    }
}

#[test]
fn test_store_deref_pointer() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    let int_type_id = builder.add_type(MirType::I32);
    let ptr_type_id = builder.add_type(MirType::Pointer { pointee: int_type_id });
    let void_type_id = builder.add_type(MirType::Void);

    let func_id = builder.define_function(
        NameId::new("main"),
        vec![],
        void_type_id,
        false,
        crate::mir::MirLinkage::Export,
    );
    builder.set_current_function(func_id);

    let entry_block_id = builder.create_block();
    builder.set_current_block(entry_block_id);
    builder.set_function_entry_block(func_id, entry_block_id);

    let local_x_id = builder.create_local(Some(NameId::new("x")), int_type_id, false);
    let local_p_id = builder.create_local(Some(NameId::new("p")), ptr_type_id, false);

    let const_42_id = builder.create_constant(int_type_id, ConstValueKind::Int(42));
    let const_10_id = builder.create_constant(int_type_id, ConstValueKind::Int(10));

    // x = 10
    builder.add_statement(MirStmt::Assign(
        Place::Local(local_x_id),
        Rvalue::Use(Operand::Constant(const_10_id)),
    ));

    // p = &x
    builder.add_statement(MirStmt::Assign(
        Place::Local(local_p_id),
        Rvalue::Use(Operand::AddressOf(Box::new(Place::Local(local_x_id)))),
    ));

    // *p = 42
    builder.add_statement(MirStmt::Store(
        Operand::Constant(const_42_id),
        Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(local_p_id))))),
    ));

    builder.set_terminator(Terminator::Return(None));

    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            insta::assert_snapshot!(clif_ir, @"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 4
                ss1 = explicit_slot 8

            block0:
                v0 = iconst.i32 10
                v6 = stack_addr.i64 ss0
                store notrap v0, v6  ; v0 = 10
                v1 = stack_addr.i64 ss0
                v5 = stack_addr.i64 ss1
                store notrap v1, v5
                v2 = iconst.i32 42
                v4 = stack_addr.i64 ss1
                v3 = load.i64 notrap v4
                store v2, v3  ; v2 = 42
                return
            }
            ");
        }
        Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump, got object file"),
        Err(e) => panic!("MIR to Cranelift lowering failed: {}", e),
    }
}

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
        ss0 = explicit_slot 4
        ss1 = explicit_slot 4
        ss2 = explicit_slot 4
        ss3 = explicit_slot 4
        ss4 = explicit_slot 4
        ss5 = explicit_slot 4

    block0:
        v0 = iconst.i32 4
        v48 = stack_addr.i64 ss0
        store notrap v0, v48  ; v0 = 4
        v47 = stack_addr.i64 ss0
        v1 = load.i32 notrap v47
        v2 = iconst.i32 0
        v3 = icmp eq v1, v2  ; v2 = 0
        v4 = iconst.i32 1
        v5 = iconst.i32 0
        v6 = select v3, v4, v5  ; v4 = 1, v5 = 0
        v46 = stack_addr.i64 ss1
        store notrap v6, v46
        v45 = stack_addr.i64 ss1
        v7 = load.i32 notrap v45
        v8 = iconst.i32 0
        v9 = icmp ne v7, v8  ; v8 = 0
        v10 = iconst.i32 1
        v11 = iconst.i32 0
        v12 = select v9, v10, v11  ; v10 = 1, v11 = 0
        v44 = stack_addr.i64 ss2
        store notrap v12, v44
        v43 = stack_addr.i64 ss2
        v13 = load.i32 notrap v43
        brif v13, block1, block2

    block2:
        jump block3

    block3:
        v42 = stack_addr.i64 ss0
        v14 = load.i32 notrap v42
        v15 = iconst.i32 0
        v16 = icmp eq v14, v15  ; v15 = 0
        v17 = iconst.i32 1
        v18 = iconst.i32 0
        v19 = select v16, v17, v18  ; v17 = 1, v18 = 0
        v41 = stack_addr.i64 ss3
        store notrap v19, v41
        v40 = stack_addr.i64 ss3
        v20 = load.i32 notrap v40
        v21 = iconst.i32 0
        v22 = icmp eq v20, v21  ; v21 = 0
        v23 = iconst.i32 1
        v24 = iconst.i32 0
        v25 = select v22, v23, v24  ; v23 = 1, v24 = 0
        v39 = stack_addr.i64 ss4
        store notrap v25, v39
        v38 = stack_addr.i64 ss4
        v26 = load.i32 notrap v38
        v27 = iconst.i32 1
        v28 = icmp ne v26, v27  ; v27 = 1
        v29 = iconst.i32 1
        v30 = iconst.i32 0
        v31 = select v28, v29, v30  ; v29 = 1, v30 = 0
        v37 = stack_addr.i64 ss5
        store notrap v31, v37
        v36 = stack_addr.i64 ss5
        v32 = load.i32 notrap v36
        brif v32, block4, block5

    block5:
        jump block6

    block6:
        v33 = iconst.i32 0
        return v33  ; v33 = 0

    block4:
        v34 = iconst.i32 1
        return v34  ; v34 = 1

    block1:
        v35 = iconst.i32 1
        return v35  ; v35 = 1
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
        ss1 = explicit_slot 2

    block0:
        v0 = f64const 0x1.8400000000000p6
        v1 = fcvt_to_uint.i32 v0  ; v0 = 0x1.8400000000000p6
        v2 = ireduce.i8 v1
        v8 = stack_addr.i64 ss0
        store notrap v2, v8
        v3 = f64const 0x1.8800000000000p6
        v4 = fcvt_to_uint.i32 v3  ; v3 = 0x1.8800000000000p6
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
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Setup Type F128
    let f128_type_id = builder.add_type(MirType::F128);
    let void_type_id = builder.add_type(MirType::Void);

    // Function
    let func_id = builder.define_function(
        NameId::new("main"),
        vec![],
        void_type_id,
        false,
        crate::mir::MirLinkage::Export,
    );
    builder.set_current_function(func_id);
    let block_id = builder.create_block();
    builder.set_current_block(block_id);
    builder.set_function_entry_block(func_id, block_id);

    // Create F128 constant from f64 value
    let const_id = builder.create_constant(f128_type_id, ConstValueKind::Float(34.1));

    // Create a local to hold it
    let local_id = builder.create_local(None, f128_type_id, false);

    // Store it
    builder.add_statement(MirStmt::Store(Operand::Constant(const_id), Place::Local(local_id)));

    builder.set_terminator(Terminator::Return(None));

    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            insta::assert_snapshot!(clif_ir, @"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 16
                gv0 = symbol colocated userextname0

            block0:
                v0 = symbol_value.i64 gv0
                v1 = load.f128 readonly v0
                v2 = stack_addr.i64 ss0
                store notrap v1, v2
                return
            }
            ");
        }
        Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump"),
        Err(e) => panic!("Error: {}", e),
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
