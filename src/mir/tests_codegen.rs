//! Tests for MIR to Cranelift IR lowering
//!
//! This module contains tests for the `MirToCraneliftLowerer` implementation.
use crate::ast::NameId;
use crate::driver::compiler::SemaOutput;
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
use crate::mir::{
    ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId, MirModule, MirModuleId,
    MirStmt, MirStmtId, MirType, Operand, Place, Terminator, TypeId,
};
use hashbrown::HashMap;

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
    let local_x = Local::new(local_id, Some(NameId::new("x")), int_type_id, false);
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
    let mut main_func = MirFunction::new_defined(func_id, NameId::new("main"), void_type_id);
    main_func.locals.push(local_id);
    main_func.entry_block = Some(entry_block_id);
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
    types.insert(
        int_type_id,
        MirType::Int {
            width: 32,
            is_signed: true,
        },
    );
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
    locals.insert(
        local_x_id,
        Local::new(local_x_id, Some(NameId::new("x")), int_type_id, false),
    );
    locals.insert(
        local_p_id,
        Local::new(local_p_id, Some(NameId::new("p")), ptr_type_id, false),
    );

    let mut statements = HashMap::new();
    let stmt1_id = MirStmtId::new(1).unwrap();
    let stmt2_id = MirStmtId::new(2).unwrap();
    let stmt3_id = MirStmtId::new(3).unwrap();
    // x = 10
    statements.insert(
        stmt1_id,
        MirStmt::Assign(
            Place::Local(local_x_id),
            crate::mir::Rvalue::Use(Operand::Constant(const_10_id)),
        ),
    );
    // p = &x
    statements.insert(
        stmt2_id,
        MirStmt::Assign(
            Place::Local(local_p_id),
            crate::mir::Rvalue::Use(Operand::AddressOf(Box::new(Place::Local(local_x_id)))),
        ),
    );
    // *p = 42
    statements.insert(
        stmt3_id,
        MirStmt::Store(
            Operand::Constant(const_42_id),
            Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(local_p_id))))),
        ),
    );

    let mut blocks = HashMap::new();
    let entry_block_id = MirBlockId::new(1).unwrap();
    let mut entry_block = MirBlock::new(entry_block_id);
    entry_block.statements.extend(vec![stmt1_id, stmt2_id, stmt3_id]);
    entry_block.terminator = Terminator::Return(None);
    blocks.insert(entry_block_id, entry_block);

    let mut functions = HashMap::new();
    let func_id = MirFunctionId::new(1).unwrap();
    let mut main_func = MirFunction::new_defined(func_id, NameId::new("main"), void_type_id);
    main_func.locals.extend(vec![local_x_id, local_p_id]);
    main_func.entry_block = Some(entry_block_id);
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

use crate::driver::{CompilerDriver, cli::CompileConfig, compiler::CompilePhase};

/// setup test with output is cranelift ir
fn setup_cranelift(c_code: &str) -> String {
    let config = CompileConfig::from_virtual_file(c_code.to_string(), CompilePhase::Cranelift);
    let mut driver = CompilerDriver::from_config(config);

    let pipeline_result = driver.run_pipeline(CompilePhase::Cranelift);
    match pipeline_result {
        Err(_) => {
            driver.print_diagnostics();
            panic!("Compilation failed");
        }
        Ok(outputs) => {
            let artifact = outputs.units.values().next().unwrap();
            let clif_dump = artifact.clif_dump.as_ref().unwrap();
            clif_dump.to_string()
        }
    }
}

#[test]
fn test_compile_struct_pointer_access() {
    let source = r#"
            int main() {
                struct S { int x; int y; } s;
                struct S *p;
                p = &s;
                s.x = 1;
                p->y = 2;
                return p->y + p->x - 3;
            }
        "#;
    let clif_dump = setup_cranelift(source);
    insta::assert_snapshot!(
        clif_dump,
        @r"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 8
        ss1 = explicit_slot 8
        ss2 = explicit_slot 4
        ss3 = explicit_slot 4

    block0:
        v0 = stack_addr.i64 ss0
        v29 = stack_addr.i64 ss1
        store notrap v0, v29
        v1 = iconst.i32 1
        v2 = stack_addr.i64 ss0
        v3 = iconst.i64 0
        v4 = iadd v2, v3  ; v3 = 0
        store v1, v4  ; v1 = 1
        v5 = iconst.i32 2
        v28 = stack_addr.i64 ss1
        v6 = load.i64 notrap v28
        v7 = iconst.i64 4
        v8 = iadd v6, v7  ; v7 = 4
        store v5, v8  ; v5 = 2
        v27 = stack_addr.i64 ss1
        v9 = load.i64 notrap v27
        v10 = iconst.i64 4
        v11 = iadd v9, v10  ; v10 = 4
        v12 = load.i32 v11
        v26 = stack_addr.i64 ss1
        v13 = load.i64 notrap v26
        v14 = iconst.i64 0
        v15 = iadd v13, v14  ; v14 = 0
        v16 = load.i32 v15
        v17 = iadd v12, v16
        v25 = stack_addr.i64 ss2
        store notrap v17, v25
        v24 = stack_addr.i64 ss2
        v18 = load.i32 notrap v24
        v19 = iconst.i32 3
        v20 = isub v18, v19  ; v19 = 3
        v23 = stack_addr.i64 ss3
        store notrap v20, v23
        v22 = stack_addr.i64 ss3
        v21 = load.i32 notrap v22
        return v21
    }
    "
    );
}

#[test]
fn test_compile_union_field_access() {
    let source = r#"
            int main() {
                union U { int a; int b; } u;
                u.a = 1;
                u.b = 3;
                if (u.a != 3 || u.b != 3)
                    return 1;
                return 0;
            }
        "#;

    let clif_dump = setup_cranelift(source);
    println!("{}", clif_dump);

    // Expect loads/stores with zero offset (union fields share offset 0)
    assert!(
        clif_dump.contains("iconst.i64 0"),
        "expected zero offset constant in IR"
    );
    assert!(clif_dump.contains("store"), "expected store instruction in IR");
    assert!(clif_dump.contains("load"), "expected load instruction in IR");
}

#[test]
fn test_alloc_dealloc_codegen() {
    // 1. Set up MIR for:
    // fn main() {
    //   let p: *mut i32;
    //   p = alloc(i32);
    //   dealloc(p);
    // }
    let mut types = HashMap::new();
    let int_type_id = TypeId::new(1).unwrap();
    let ptr_type_id = TypeId::new(2).unwrap();
    let void_type_id = TypeId::new(3).unwrap();
    types.insert(
        int_type_id,
        MirType::Int {
            width: 32,
            is_signed: true,
        },
    );
    types.insert(ptr_type_id, MirType::Pointer { pointee: int_type_id });
    types.insert(void_type_id, MirType::Void);

    let mut locals = HashMap::new();
    let local_p_id = LocalId::new(1).unwrap();
    locals.insert(
        local_p_id,
        Local::new(local_p_id, Some(NameId::new("p")), ptr_type_id, false),
    );

    let mut statements = HashMap::new();
    let alloc_stmt_id = MirStmtId::new(1).unwrap();
    let dealloc_stmt_id = MirStmtId::new(2).unwrap();

    // p = alloc(...)
    statements.insert(alloc_stmt_id, MirStmt::Alloc(Place::Local(local_p_id), int_type_id));
    // dealloc(p)
    statements.insert(
        dealloc_stmt_id,
        MirStmt::Dealloc(Operand::Copy(Box::new(Place::Local(local_p_id)))),
    );

    let mut blocks = HashMap::new();
    let entry_block_id = MirBlockId::new(1).unwrap();
    let mut entry_block = MirBlock::new(entry_block_id);
    entry_block.statements.push(alloc_stmt_id);
    entry_block.statements.push(dealloc_stmt_id);
    entry_block.terminator = Terminator::Return(None);
    blocks.insert(entry_block_id, entry_block);

    let mut functions = HashMap::new();
    let func_id = MirFunctionId::new(1).unwrap();
    let mut main_func = MirFunction::new_defined(func_id, NameId::new("main"), void_type_id);
    main_func.locals.push(local_p_id);
    main_func.entry_block = Some(entry_block_id);
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
        constants: HashMap::new(),
        statements,
    };

    let lowerer = MirToCraneliftLowerer::new(sema_output);
    let result = lowerer.compile_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            insta::assert_snapshot!(clif_ir, @r"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 8
                sig0 = (i64) -> i64 system_v
                sig1 = (i64) system_v
                fn0 = u0:0 sig0
                fn1 = u0:1 sig1

            block0:
                v0 = iconst.i64 4
                v1 = call fn0(v0)  ; v0 = 4
                v4 = stack_addr.i64 ss0
                store notrap v1, v4
                v3 = stack_addr.i64 ss0
                v2 = load.i64 notrap v3
                call fn1(v2)
                return
            }
            ");
        }
        Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump, got object file"),
        Err(e) => panic!("MIR to Cranelift lowering failed: {}", e),
    }
}
