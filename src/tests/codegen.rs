//! Tests for MIR to Cranelift IR lowering
//!
//! This module contains tests for the `MirToCraneliftLowerer` implementation.
use crate::ast::NameId;

use crate::driver::artifact::CompilePhase;
use crate::mir::codegen::{ClifOutput, EmitContext, EmitKind, MirToCraneliftLowerer, emit_const};
use crate::mir::{CallTarget, LocalId};
use crate::mir::{MirModuleId, MirRecordLayout, MirStmt, MirType, Operand, Place, Terminator};
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
    let const_1_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(0x11111111));
    let const_2_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(0x22222222));

    let struct_const_kind = crate::mir::ConstValueKind::StructLiteral(vec![(0, const_1_id), (1, const_2_id)]);
    let struct_const_id = builder.create_constant(struct_type_id, struct_const_kind);

    // 3. Get MirProgram
    let sema_output = builder.consume();

    // 4. Emit Constant
    let mut output = Vec::new();
    let ctx = EmitContext {
        mir: &sema_output,
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
    let const_val_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(42));

    // 5. Create Statement: store 42 into x
    let store_stmt = MirStmt::Store(Operand::Constant(const_val_id), Place::Local(local_id));
    builder.add_statement(store_stmt);

    builder.set_terminator(Terminator::Return(None));

    // 6. Compile
    let sema_output = builder.consume();
    let lowerer = MirToCraneliftLowerer::new(sema_output);
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

    let const_42_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(42));
    let const_10_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(10));

    // x = 10
    builder.add_statement(MirStmt::Assign(
        Place::Local(local_x_id),
        crate::mir::Rvalue::Use(Operand::Constant(const_10_id)),
    ));

    // p = &x
    builder.add_statement(MirStmt::Assign(
        Place::Local(local_p_id),
        crate::mir::Rvalue::Use(Operand::AddressOf(Box::new(Place::Local(local_x_id)))),
    ));

    // *p = 42
    builder.add_statement(MirStmt::Store(
        Operand::Constant(const_42_id),
        Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(local_p_id))))),
    ));

    builder.set_terminator(Terminator::Return(None));

    let sema_output = builder.consume();
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

use crate::tests::semantic_common::setup_cranelift;

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
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    let int_type_id = builder.add_type(MirType::I32);
    let ptr_type_id = builder.add_type(MirType::Pointer { pointee: int_type_id });
    let void_type_id = builder.add_type(MirType::Void);

    let func_id = builder.define_function(NameId::new("main"), vec![], void_type_id, false);
    builder.set_current_function(func_id);

    let entry_block_id = builder.create_block();
    builder.set_current_block(entry_block_id);
    builder.set_function_entry_block(func_id, entry_block_id);

    let local_p_id = builder.create_local(Some(NameId::new("p")), ptr_type_id, false);

    // p = alloc(...)
    builder.add_statement(MirStmt::Alloc(Place::Local(local_p_id), int_type_id));

    // dealloc(p)
    builder.add_statement(MirStmt::Dealloc(Operand::Copy(Box::new(Place::Local(local_p_id)))));

    builder.set_terminator(Terminator::Return(None));

    let sema_output = builder.consume();
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
                fn0 = u0:1 sig0
                fn1 = u0:2 sig1

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

#[test]
fn test_indirect_function_call() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Setup Types
    let int_type_id = builder.add_type(MirType::I32);

    // fn(i32) -> i32
    let func_type_id = builder.add_type(MirType::Function {
        return_type: int_type_id,
        params: vec![int_type_id],
    });

    // *fn(i32) -> i32
    let func_ptr_type_id = builder.add_type(MirType::Pointer { pointee: func_type_id });

    // Setup Function 1 (Target): fn target(x: i32) -> i32 { return x; }
    // Use define_function which accepts Vec<TypeId> for params
    let target_func_id = builder.define_function(
        NameId::new("target"),
        vec![int_type_id], // param types
        int_type_id,       // return type
        false,             // not variadic
    );

    builder.set_current_function(target_func_id);
    let target_block_id = builder.create_block();
    builder.set_current_block(target_block_id);
    builder.set_function_entry_block(target_func_id, target_block_id);

    // Get the param local ID (created by define_function)
    // Since we are defining it manually via `define_function` which adds one param,
    // and it's the first function in this builder, we know the LocalId is 1.
    // We do not need to consume and inspect because we are constructing it.
    let param_id = LocalId::new(1).unwrap();

    builder.set_terminator(Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(
        param_id,
    ))))));

    // Setup Function 2 (Main): fn main() -> i32
    let main_func_id = builder.define_function(NameId::new("main"), vec![], int_type_id, false);

    builder.set_current_function(main_func_id);
    let main_block_id = builder.create_block();
    builder.set_current_block(main_block_id);
    builder.set_function_entry_block(main_func_id, main_block_id);

    // Local: ptr: *fn(i32) -> i32
    let ptr_local_id = builder.create_local(Some(NameId::new("ptr")), func_ptr_type_id, false);

    // Constants
    let func_addr_const_id = builder.create_constant(
        func_ptr_type_id,
        crate::mir::ConstValueKind::FunctionAddress(target_func_id),
    );
    let arg_const_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(42));

    // 1. ptr = &target
    builder.add_statement(MirStmt::Assign(
        Place::Local(ptr_local_id),
        crate::mir::Rvalue::Use(Operand::Constant(func_addr_const_id)),
    ));

    // 2. call(*ptr)(42)
    let temp_local_id = builder.create_local(Some(NameId::new("temp")), int_type_id, false);

    builder.add_statement(MirStmt::Call {
        target: CallTarget::Indirect(Operand::Copy(Box::new(Place::Local(ptr_local_id)))),
        args: vec![Operand::Constant(arg_const_id)],
        dest: Some(Place::Local(temp_local_id)),
    });

    builder.set_terminator(Terminator::Return(Some(Operand::Copy(Box::new(Place::Local(
        temp_local_id,
    ))))));

    // Compile
    let sema_output = builder.consume();
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
fn test_global_function_pointer_init() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Define function type: fn(i32) -> i32
    let int_type_id = builder.add_type(MirType::I32);
    let func_type_id = builder.add_type(MirType::Function {
        return_type: int_type_id,
        params: vec![int_type_id],
    });
    let func_ptr_type_id = builder.add_type(MirType::Pointer { pointee: func_type_id });

    // Define target function
    let target_func_id = builder.define_function(NameId::new("target"), vec![int_type_id], int_type_id, false);
    builder.set_current_function(target_func_id);
    let block_id = builder.create_block();
    builder.set_current_block(block_id);
    builder.set_function_entry_block(target_func_id, block_id);

    let zero_const_id = builder.create_constant(int_type_id, crate::mir::ConstValueKind::Int(0));
    builder.set_terminator(Terminator::Return(Some(Operand::Constant(zero_const_id))));

    // Create global variable "ptr" initialized with address of "target"
    let func_addr_const_id = builder.create_constant(
        func_ptr_type_id,
        crate::mir::ConstValueKind::FunctionAddress(target_func_id),
    );
    let _global_id =
        builder.create_global_with_init(NameId::new("ptr"), func_ptr_type_id, false, Some(func_addr_const_id));

    // Compile
    let sema_output = builder.consume();
    let lowerer = MirToCraneliftLowerer::new(sema_output);
    let result = lowerer.compile_module(EmitKind::Clif);

    match result {
        Ok(_) => (), // Success if no panic
        Err(e) => panic!("Compilation failed: {}", e),
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
