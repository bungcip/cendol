//! Tests for function calls
use crate::ast::NameId;
use crate::codegen::{ClifGen, ClifOutput, EmitKind};
use crate::mir::{CallTarget, MirModuleId, MirStmt, MirType, Operand, Place, Terminator};
use crate::tests::test_utils;

#[test]
fn test_indirect_function_call() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Setup Types
    let int_type_id = builder.add_type(MirType::I32);

    // fn(i32) -> i32
    let func_type_id = builder.add_type(MirType::Function {
        return_type: int_type_id,
        params: vec![int_type_id],
        is_variadic: false,
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
    let param_id = crate::mir::LocalId::new(1).unwrap();

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
    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    match result {
        ClifOutput::ClifDump(clif_ir) => {
            insta::assert_snapshot!(test_utils::sort_clif_ir(&clif_ir), @r"
            ; Function: main
            function u0:0() -> i32 system_v {
                ss0 = explicit_slot 8
                ss1 = explicit_slot 4
                sig0 = (i32) -> i32 system_v
                sig1 = (i32) -> i32 system_v
                fn0 = colocated u0:0 sig0

            block0:
                v0 = func_addr.i64 fn0
                v8 = stack_addr.i64 ss0
                store notrap v0, v8
                v7 = stack_addr.i64 ss0
                v1 = load.i64 notrap v7
                v2 = iconst.i32 42
                v3 = call_indirect sig1, v1(v2)  ; v2 = 42
                v6 = stack_addr.i64 ss1
                store notrap v3, v6
                v5 = stack_addr.i64 ss1
                v4 = load.i32 notrap v5
                return v4
            }

            ; Function: target
            function u0:0(i32) -> i32 system_v {
                ss0 = explicit_slot 4

            block0(v0: i32):
                v3 = stack_addr.i64 ss0
                store notrap v0, v3
                v2 = stack_addr.i64 ss0
                v1 = load.i32 notrap v2
                return v1
            }
            ");
        }
        ClifOutput::ObjectFile(_) => panic!("Expected Clif dump"),
    }
}

#[test]
fn test_global_function_pointer_init() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Define function type: fn(i32) -> i32
    let int_type_id = builder.add_type(MirType::I32);
    let func_type_id = builder.add_type(MirType::Function {
        return_type: int_type_id,
        params: vec![int_type_id],
        is_variadic: false,
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
    let mir = builder.consume();
    let lowerer = ClifGen::new(mir);
    let result = lowerer.visit_module(EmitKind::Clif);

    match result {
        ClifOutput::ClifDump(clif_ir) => {
            insta::assert_snapshot!(test_utils::sort_clif_ir(&clif_ir), @r"
            ; Function: target
            function u0:0(i32) -> i32 system_v {
                ss0 = explicit_slot 4

            block0(v0: i32):
                v2 = stack_addr.i64 ss0
                store notrap v0, v2
                v1 = iconst.i32 0
                return v1  ; v1 = 0
            }
            ");
        }
        ClifOutput::ObjectFile(_) => panic!("Expected Clif dump"),
    }
}
