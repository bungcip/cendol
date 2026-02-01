//! Basic MIR to Cranelift IR lowering tests
use crate::ast::NameId;
use crate::driver::artifact::CompilePhase;
use crate::mir::codegen::{ClifOutput, EmitContext, EmitKind, MirToCraneliftLowerer, emit_const};
use crate::mir::{ConstValueKind, Rvalue};
use crate::mir::{MirModuleId, MirRecordLayout, MirStmt, MirType, Operand, Place, Terminator};
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::semantic_common::run_pass;

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
    let expected = vec![0x11, 0x11, 0x11, 0x11, 0x22, 0x22, 0x22, 0x22];

    assert_eq!(
        output.len(),
        8,
        "Output size mismatch. Expected 8 bytes, got {}",
        output.len()
    );
    assert_eq!(output, expected, "Output content mismatch");
}

#[test]
fn test_store_statement_lowering() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // 1. Set up Types
    let int_type_id = builder.add_type(MirType::I32);
    let void_type_id = builder.add_type(MirType::Void);

    // 2. Set up Function and Block
    let func_id = builder.define_function(NameId::new("main"), vec![], void_type_id, false);
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
    let lowerer = MirToCraneliftLowerer::new(mir);
    let result = lowerer.compile_module(EmitKind::Clif);

    // 7. Assert
    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            println!("{}", clif_ir); // for debugging
            // Check that we are calculating the stack address and then storing to it.
            assert!(clif_ir.contains("iconst.i32 42"));
            assert!(clif_ir.contains("stack_addr"));
            assert!(clif_ir.contains("store"));
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

    let func_id = builder.define_function(NameId::new("main"), vec![], void_type_id, false);
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
    let lowerer = MirToCraneliftLowerer::new(mir);
    let result = lowerer.compile_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            println!("{}", clif_ir);
            // Check that we load the pointer's value (an address) from its stack slot,
            // and then perform a general `store` to that address.
            assert!(clif_ir.contains("load"));
            assert!(clif_ir.contains("iconst.i32 42"));
            // Check that a general store is used.
            assert!(clif_ir.contains("store"));
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
    println!("{}", clif_dump);

    // Check for 'select' instructions which we used to fix the uextend issue
    assert!(
        clif_dump.contains("select"),
        "Expected select instruction for boolean conversion"
    );
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
    println!("{}", clif_dump);

    // Check for 'ireduce' instructions which we used to fix the crash
    assert!(
        clif_dump.contains("ireduce.i8"),
        "Expected ireduce.i8 instruction for float->char conversion"
    );
    assert!(
        clif_dump.contains("ireduce.i16"),
        "Expected ireduce.i16 instruction for float->short conversion"
    );
}

#[test]
fn test_f128_constant_promotion() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Setup Type F128
    let f128_type_id = builder.add_type(MirType::F128);
    let void_type_id = builder.add_type(MirType::Void);

    // Function
    let func_id = builder.define_function(NameId::new("main"), vec![], void_type_id, false);
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
    let lowerer = MirToCraneliftLowerer::new(mir);
    let result = lowerer.compile_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            println!("{}", clif_ir);
            // Verify load from memory is used instead of fpromote
            assert!(clif_ir.contains("load.f128"), "Expected load.f128 instruction");
            assert!(
                clif_ir.contains("global_value") || clif_ir.contains("symbol_value"),
                "Expected global_value or symbol_value instruction"
            );
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
