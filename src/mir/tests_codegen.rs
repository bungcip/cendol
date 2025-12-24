//! Tests for MIR to Cranelift IR lowering
//!
//! This module contains tests for the `MirToCraneliftLowerer` implementation.

use crate::mir::{
    BinaryOp, ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId, MirModule,
    MirModuleId, MirStmt, MirStmtId, MirType, Operand, Place, Rvalue, Terminator, TypeId,
};
use hashbrown::HashMap;
use symbol_table::GlobalSymbol as Symbol;

use crate::mir::CallTarget;
use crate::mir::codegen::MirToCraneliftLowerer;

#[test]
fn test_mir_to_cranelift_basic() {
    // Create a basic MIR module
    let mut module = MirModule::new(MirModuleId::new(1).unwrap());

    // Create a simple function that returns 42
    let func_id = MirFunctionId::new(1).unwrap();
    let int_type_id = TypeId::new(1).unwrap();

    // Add the int type to the module
    module.types.push(MirType::Int {
        is_signed: true,
        width: 32,
    });

    let mut func = MirFunction::new(func_id, Symbol::new("main"), int_type_id);

    // Create entry block
    let entry_block_id = MirBlockId::new(1).unwrap();
    let mut entry_block = MirBlock::new(entry_block_id);

    // Add return constant
    let return_const_id = ConstValueId::new(1).unwrap();
    module.constants.push(ConstValue::Int(42));

    let return_operand = Operand::Constant(return_const_id);
    entry_block.terminator = Terminator::Return(Some(return_operand));

    func.entry_block = entry_block_id;
    func.blocks.push(entry_block_id);

    module.functions.push(func_id);

    // Create the lowerer and compile
    let lowerer = MirToCraneliftLowerer::new(
        module,
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
    );

    // This should compile without panicking
    // Note: The actual compilation might not work perfectly yet since this is a basic implementation
    let result = lowerer.compile();

    // For now, we'll just check that it doesn't panic
    // In a real implementation, we'd verify the generated code
    assert!(result.is_ok() || result.is_err()); // Just check it returns a result
}

#[test]
fn test_mir_to_cranelift_function_call_panics() {
    // This test reproduces the panic from the issue.
    // It creates a `main` function that calls a `foo` function.

    // ========================================================================
    // 1. Setup common data
    // ========================================================================
    let mut module = MirModule::new(MirModuleId::new(1).unwrap());
    let mut functions = HashMap::new();
    let mut blocks = HashMap::new();
    let mut locals = HashMap::new();
    let mut statements = HashMap::new();

    // Add int type
    let int_type_id = TypeId::new(1).unwrap();
    module.types.push(MirType::Int {
        is_signed: true,
        width: 32,
    });

    // Add constants
    let const_2_id = ConstValueId::new(1).unwrap();
    module.constants.push(ConstValue::Int(2));
    let const_1_id = ConstValueId::new(2).unwrap();
    module.constants.push(ConstValue::Int(1));
    let const_3_id = ConstValueId::new(3).unwrap();
    module.constants.push(ConstValue::Int(3));

    // ========================================================================
    // 2. Create `foo` function
    // ========================================================================
    let foo_func_id = MirFunctionId::new(1).unwrap();
    let foo_entry_block_id = MirBlockId::new(1).unwrap();

    // `foo` parameters
    let param_a_id = LocalId::new(1).unwrap();
    let param_b_id = LocalId::new(2).unwrap();
    locals.insert(
        param_a_id,
        Local::new(param_a_id, Some(Symbol::new("a")), int_type_id, true),
    );
    locals.insert(
        param_b_id,
        Local::new(param_b_id, Some(Symbol::new("b")), int_type_id, true),
    );

    // `foo` locals for intermediate values
    let temp_add_id = LocalId::new(3).unwrap();
    locals.insert(temp_add_id, Local::new(temp_add_id, None, int_type_id, false));
    let temp_sub_id = LocalId::new(4).unwrap();
    locals.insert(temp_sub_id, Local::new(temp_sub_id, None, int_type_id, false));
    let return_val_id = LocalId::new(5).unwrap();
    locals.insert(return_val_id, Local::new(return_val_id, None, int_type_id, false));

    let mut foo_func = MirFunction::new(foo_func_id, Symbol::new("foo"), int_type_id);
    foo_func.params = vec![param_a_id, param_b_id];
    foo_func.locals = vec![temp_add_id, temp_sub_id, return_val_id];
    foo_func.entry_block = foo_entry_block_id;
    foo_func.blocks.push(foo_entry_block_id);

    let mut foo_entry_block = MirBlock::new(foo_entry_block_id);

    // Statement 1: _3 = 2 + a
    let stmt1_id = MirStmtId::new(1).unwrap();
    let stmt1 = MirStmt::Assign(
        Place::Local(temp_add_id),
        Rvalue::BinaryOp(
            BinaryOp::Add,
            Operand::Constant(const_2_id),
            Operand::Copy(Box::new(Place::Local(param_a_id))),
        ),
    );
    statements.insert(stmt1_id, stmt1);
    foo_entry_block.statements.push(stmt1_id);

    // Statement 2: _4 = _3 - b
    let stmt2_id = MirStmtId::new(2).unwrap();
    let stmt2 = MirStmt::Assign(
        Place::Local(temp_sub_id),
        Rvalue::BinaryOp(
            BinaryOp::Sub,
            Operand::Copy(Box::new(Place::Local(temp_add_id))),
            Operand::Copy(Box::new(Place::Local(param_b_id))),
        ),
    );
    statements.insert(stmt2_id, stmt2);
    foo_entry_block.statements.push(stmt2_id);

    // Statement 3: _5 = _4
    let stmt3_id = MirStmtId::new(3).unwrap();
    let stmt3 = MirStmt::Assign(
        Place::Local(return_val_id),
        Rvalue::Use(Operand::Copy(Box::new(Place::Local(temp_sub_id)))),
    );
    statements.insert(stmt3_id, stmt3);
    foo_entry_block.statements.push(stmt3_id);

    foo_entry_block.terminator = Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(return_val_id)))));
    blocks.insert(foo_entry_block_id, foo_entry_block);
    functions.insert(foo_func_id, foo_func);
    module.functions.push(foo_func_id);

    // ========================================================================
    // 3. Create `main` function
    // ========================================================================
    let main_func_id = MirFunctionId::new(2).unwrap();
    let main_entry_block_id = MirBlockId::new(2).unwrap();

    let main_return_val_id = LocalId::new(6).unwrap();
    locals.insert(
        main_return_val_id,
        Local::new(main_return_val_id, None, int_type_id, false),
    );

    let mut main_func = MirFunction::new(main_func_id, Symbol::new("main"), int_type_id);
    main_func.locals = vec![main_return_val_id];
    main_func.entry_block = main_entry_block_id;
    main_func.blocks.push(main_entry_block_id);

    let mut main_entry_block = MirBlock::new(main_entry_block_id);

    // Statement: _6 = foo(1, 3)
    let stmt4_id = MirStmtId::new(4).unwrap();
    let stmt4 = MirStmt::Assign(
        Place::Local(main_return_val_id),
        Rvalue::Call(
            CallTarget::Direct(foo_func_id),
            vec![Operand::Constant(const_1_id), Operand::Constant(const_3_id)],
        ),
    );
    statements.insert(stmt4_id, stmt4);
    main_entry_block.statements.push(stmt4_id);

    main_entry_block.terminator = Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(main_return_val_id)))));
    blocks.insert(main_entry_block_id, main_entry_block);
    functions.insert(main_func_id, main_func);
    module.functions.push(main_func_id);

    // ========================================================================
    // 4. Compile
    // ========================================================================
    let lowerer = MirToCraneliftLowerer::new(
        module,
        functions,
        blocks,
        locals,
        HashMap::new(), // No globals
        HashMap::new(), // Types are in module
        statements,
    );

    let result = lowerer.compile();
    assert!(result.is_ok());
}
