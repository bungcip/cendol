//! Tests for MIR to Cranelift IR lowering
//!
//! This module contains tests for the `MirToCraneliftLowerer` implementation.
use crate::ast::NameId;
use crate::mir::MirProgram;
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer, emit_const};
use crate::mir::{
    ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId, MirModule, MirModuleId,
    MirRecordLayout, MirStmt, MirStmtId, MirType, Operand, Place, Terminator, TypeId,
};
use hashbrown::HashMap;

#[test]
fn test_emit_const_struct_literal() {
    // 1. Setup Types
    let mut types = HashMap::new();
    let int_type_id = TypeId::new(1).unwrap();
    types.insert(int_type_id, MirType::I32);

    let struct_type_id = TypeId::new(2).unwrap();
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
    types.insert(struct_type_id, struct_type.clone());

    // 2. Setup Constants
    let mut constants = HashMap::new();
    let const_1_id = ConstValueId::new(1).unwrap();
    constants.insert(const_1_id, ConstValue::Int(0x11111111));
    let const_2_id = ConstValueId::new(2).unwrap();
    constants.insert(const_2_id, ConstValue::Int(0x22222222));

    let struct_const_id = ConstValueId::new(3).unwrap();
    let struct_const = ConstValue::StructLiteral(vec![(0, const_1_id), (1, const_2_id)]);
    constants.insert(struct_const_id, struct_const);

    // 3. Setup MirProgram context
    let mir_module = MirModule::new(MirModuleId::new(1).unwrap());

    let sema_output = MirProgram {
        module: mir_module,
        functions: HashMap::new(),
        blocks: HashMap::new(),
        locals: HashMap::new(),
        globals: HashMap::new(),
        types,
        constants,
        statements: HashMap::new(),
    };

    // 4. Emit Constant
    let mut output = Vec::new();
    emit_const(struct_const_id, &struct_type, &mut output, &sema_output).expect("emit_const failed");

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
    // 1. Set up the MIR components
    let mut types = HashMap::new();
    let int_type_id = TypeId::new(1).unwrap();
    let void_type_id = TypeId::new(2).unwrap();
    types.insert(int_type_id, MirType::I32);
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

    let sema_output = MirProgram {
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
    types.insert(int_type_id, MirType::I32);
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

    let sema_output = MirProgram {
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

use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

/// setup test with output is cranelift ir
fn setup_cranelift(c_code: &str) -> String {
    let (driver, pipeline_result) = test_utils::run_pipeline(c_code, CompilePhase::Cranelift);
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
    types.insert(int_type_id, MirType::I32);
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

    let sema_output = MirProgram {
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
#[cfg(test)]
mod tests {
    use crate::ast::NameId;
    use crate::mir::MirProgram;
    use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
    use crate::mir::{
        CallTarget, ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId,
        MirModule, MirModuleId, MirStmt, MirStmtId, MirType, Operand, Place, Terminator, TypeId,
    };
    use hashbrown::HashMap;

    #[test]
    fn test_indirect_function_call() {
        // Setup Types
        let mut types = HashMap::new();
        let int_type_id = TypeId::new(1).unwrap();
        types.insert(int_type_id, MirType::I32);

        // fn(i32) -> i32
        let func_type_id = TypeId::new(2).unwrap();
        types.insert(
            func_type_id,
            MirType::Function {
                return_type: int_type_id,
                params: vec![int_type_id],
            },
        );

        // *fn(i32) -> i32
        let func_ptr_type_id = TypeId::new(3).unwrap();
        types.insert(func_ptr_type_id, MirType::Pointer { pointee: func_type_id });

        // Setup Function 1 (Target): fn target(x: i32) -> i32 { return x; }
        let target_func_id = MirFunctionId::new(1).unwrap();
        let mut target_func = MirFunction::new_defined(target_func_id, NameId::new("target"), int_type_id);
        let param_id = LocalId::new(1).unwrap();
        target_func.params.push(param_id);

        let target_block_id = MirBlockId::new(1).unwrap();
        let mut target_block = MirBlock::new(target_block_id);
        // return param
        target_block.terminator = Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(param_id)))));
        target_func.blocks.push(target_block_id);
        target_func.entry_block = Some(target_block_id);

        // Setup Function 2 (Main): fn main() -> i32
        let main_func_id = MirFunctionId::new(2).unwrap();
        let mut main_func = MirFunction::new_defined(main_func_id, NameId::new("main"), int_type_id);

        // Local: ptr: *fn(i32) -> i32
        let ptr_local_id = LocalId::new(2).unwrap();
        let ptr_local = Local::new(ptr_local_id, Some(NameId::new("ptr")), func_ptr_type_id, false);
        main_func.locals.push(ptr_local_id);

        // Constants
        let mut constants = HashMap::new();
        let func_addr_const_id = ConstValueId::new(1).unwrap();
        constants.insert(func_addr_const_id, ConstValue::FunctionAddress(target_func_id));
        let arg_const_id = ConstValueId::new(2).unwrap();
        constants.insert(arg_const_id, ConstValue::Int(42));

        // Statements
        let mut statements = HashMap::new();

        // 1. ptr = &target
        let stmt1_id = MirStmtId::new(1).unwrap();
        statements.insert(
            stmt1_id,
            MirStmt::Assign(
                Place::Local(ptr_local_id),
                crate::mir::Rvalue::Use(Operand::Constant(func_addr_const_id)),
            ),
        );

        // 2. call(*ptr)(42)
        let temp_local_id = LocalId::new(3).unwrap();
        let temp_local = Local::new(temp_local_id, Some(NameId::new("temp")), int_type_id, false);
        main_func.locals.push(temp_local_id);

        let stmt2_id = MirStmtId::new(2).unwrap();
        statements.insert(
            stmt2_id,
            MirStmt::Assign(
                Place::Local(temp_local_id),
                crate::mir::Rvalue::Call(
                    CallTarget::Indirect(Operand::Copy(Box::new(Place::Local(ptr_local_id)))),
                    vec![Operand::Constant(arg_const_id)],
                ),
            ),
        );

        let main_block_id = MirBlockId::new(2).unwrap();
        let mut main_block = MirBlock::new(main_block_id);
        main_block.statements.push(stmt1_id);
        main_block.statements.push(stmt2_id);
        main_block.terminator = Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(temp_local_id)))));

        main_func.blocks.push(main_block_id);
        main_func.entry_block = Some(main_block_id);

        // Module
        let mut mir_module = MirModule::new(MirModuleId::new(1).unwrap());
        mir_module.functions.push(target_func_id);
        mir_module.functions.push(main_func_id);

        let mut locals_map = HashMap::new();
        locals_map.insert(
            param_id,
            Local::new(param_id, Some(NameId::new("p")), int_type_id, true),
        );
        locals_map.insert(ptr_local_id, ptr_local);
        locals_map.insert(temp_local_id, temp_local);

        let mut functions = HashMap::new();
        functions.insert(target_func_id, target_func);
        functions.insert(main_func_id, main_func);

        let mut blocks = HashMap::new();
        blocks.insert(target_block_id, target_block);
        blocks.insert(main_block_id, main_block);

        let sema_output = MirProgram {
            module: mir_module,
            functions,
            blocks,
            locals: locals_map,
            globals: HashMap::new(),
            types,
            constants,
            statements,
        };

        // Compile
        let lowerer = MirToCraneliftLowerer::new(sema_output);
        let result = lowerer.compile_module(EmitKind::Clif);

        match result {
            Ok(ClifOutput::ClifDump(clif_ir)) => {
                println!("{}", clif_ir);
                assert!(clif_ir.contains("call_indirect"), "Expected call_indirect instruction");
            }
            Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump"),
            Err(e) => panic!("Error: {}", e),
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
        let clif_dump = super::setup_cranelift(source);
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
        let clif_dump = super::setup_cranelift(source);
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
}
