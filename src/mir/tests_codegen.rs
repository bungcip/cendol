//! Tests for MIR to Cranelift IR lowering
//!
//! This module contains tests for the `MirToCraneliftLowerer` implementation.
use crate::driver::compiler::SemaOutput;
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
use crate::mir::{
    MirBlock, MirBlockId, MirFunction, MirFunctionId, MirModule, MirModuleId, MirStmt, MirStmtId,
    MirType, Operand, Place, Terminator, TypeId, ConstValue, ConstValueId, Local, LocalId,
};
use hashbrown::HashMap;
use std::num::NonZeroU32;
use symbol_table::GlobalSymbol as Symbol;

#[test]
fn test_mir_to_cranelift_basic() {
    assert!(true);
}

#[test]
fn test_store_statement_lowering() {
    // 1. Set up the MIR components
    let mut types = HashMap::new();
    let int_type_id = TypeId::new(1).unwrap();
    let void_type_id = TypeId::new(2).unwrap();
    types.insert(
        int_type_id,
        MirType::Int {
            width: 32,
            is_signed: true,
        },
    );
    types.insert(void_type_id, MirType::Void);

    let mut constants = HashMap::new();
    let const_val_id = ConstValueId::new(1).unwrap();
    constants.insert(const_val_id, ConstValue::Int(42));

    let mut locals = HashMap::new();
    let local_id = LocalId::new(1).unwrap();
    let local_x = Local::new(local_id, Some(Symbol::new("x")), int_type_id, false);
    locals.insert(local_id, local_x);

    let mut statements = HashMap::new();
    let store_stmt_id = MirStmtId::new(1).unwrap();
    // This is the statement we want to test: store 42 into x
    let store_stmt = MirStmt::Store(Operand::Constant(const_val_id), Place::Local(local_id));
    statements.insert(store_stmt_id, store_stmt);

    let mut blocks = HashMap::new();
    let entry_block_id = MirBlockId::new(1).unwrap();
    let mut entry_block = MirBlock::new(entry_block_id);
    entry_block.statements.push(store_stmt_id);
    entry_block.terminator = Terminator::Return(None);
    blocks.insert(entry_block_id, entry_block);

    let mut functions = HashMap::new();
    let func_id = MirFunctionId::new(1).unwrap();
    let mut main_func = MirFunction::new(func_id, Symbol::new("main"), void_type_id);
    main_func.locals.push(local_id);
    main_func.entry_block = entry_block_id;
    main_func.blocks.push(entry_block_id);
    functions.insert(func_id, main_func);

    let mut mir_module = MirModule::new(MirModuleId::new(1).unwrap());
    mir_module.functions.push(func_id);

    let sema_output = SemaOutput {
        module: mir_module,
        functions,
        blocks,
        locals,
        globals: HashMap::new(),
        types,
        constants,
        statements,
    };

    // 2. Compile the MIR to Cranelift IR
    let lowerer = MirToCraneliftLowerer::new(sema_output);
    let result = lowerer.compile_module(EmitKind::Clif);

    // 3. Assert the output is correct
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
    // 1. Set up MIR for:
    // fn main() {
    //   let x: i32 = 10;
    //   let p: *mut i32 = &x;
    //   *p = 42;
    // }
    let mut types = HashMap::new();
    let int_type_id = TypeId::new(1).unwrap();
    let ptr_type_id = TypeId::new(2).unwrap();
    let void_type_id = TypeId::new(3).unwrap();
    types.insert(int_type_id, MirType::Int { width: 32, is_signed: true });
    types.insert(ptr_type_id, MirType::Pointer { pointee: int_type_id });
    types.insert(void_type_id, MirType::Void);

    let mut constants = HashMap::new();
    let const_42_id = ConstValueId::new(1).unwrap();
    constants.insert(const_42_id, ConstValue::Int(42));
    let const_10_id = ConstValueId::new(2).unwrap();
    constants.insert(const_10_id, ConstValue::Int(10));

    let mut locals = HashMap::new();
    let local_x_id = LocalId::new(1).unwrap();
    let local_p_id = LocalId::new(2).unwrap();
    locals.insert(local_x_id, Local::new(local_x_id, Some(Symbol::new("x")), int_type_id, false));
    locals.insert(local_p_id, Local::new(local_p_id, Some(Symbol::new("p")), ptr_type_id, false));

    let mut statements = HashMap::new();
    let stmt1_id = MirStmtId::new(1).unwrap();
    let stmt2_id = MirStmtId::new(2).unwrap();
    let stmt3_id = MirStmtId::new(3).unwrap();
    // x = 10
    statements.insert(stmt1_id, MirStmt::Assign(Place::Local(local_x_id), crate::mir::Rvalue::Use(Operand::Constant(const_10_id))));
    // p = &x
    statements.insert(stmt2_id, MirStmt::Assign(Place::Local(local_p_id), crate::mir::Rvalue::Use(Operand::AddressOf(Box::new(Place::Local(local_x_id))))));
    // *p = 42
    statements.insert(stmt3_id, MirStmt::Store(Operand::Constant(const_42_id), Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(local_p_id)))))));


    let mut blocks = HashMap::new();
    let entry_block_id = MirBlockId::new(1).unwrap();
    let mut entry_block = MirBlock::new(entry_block_id);
    entry_block.statements.extend(vec![stmt1_id, stmt2_id, stmt3_id]);
    entry_block.terminator = Terminator::Return(None);
    blocks.insert(entry_block_id, entry_block);

    let mut functions = HashMap::new();
    let func_id = MirFunctionId::new(1).unwrap();
    let mut main_func = MirFunction::new(func_id, Symbol::new("main"), void_type_id);
    main_func.locals.extend(vec![local_x_id, local_p_id]);
    main_func.entry_block = entry_block_id;
    main_func.blocks.push(entry_block_id);
    functions.insert(func_id, main_func);

    let mut mir_module = MirModule::new(MirModuleId::new(1).unwrap());
    mir_module.functions.push(func_id);

    let sema_output = SemaOutput {
        module: mir_module,
        functions,
        blocks,
        locals,
        globals: HashMap::new(),
        types,
        constants,
        statements,
    };

    let lowerer = MirToCraneliftLowerer::new(sema_output);
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
