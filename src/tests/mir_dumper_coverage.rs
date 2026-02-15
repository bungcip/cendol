//! Test coverage for MIR dumper, covering cases not easily reachable from C source.

use crate::ast::NameId;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::mir::*;

#[test]
fn test_mir_dumper_manual_coverage() {
    let mut builder = MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    // Types
    let void_ty = builder.add_type(MirType::Void);
    let i32_ty = builder.add_type(MirType::I32);
    let f32_ty = builder.add_type(MirType::F32);
    let _f80_ty = builder.add_type(MirType::F80); // 128-bit
    let _f128_ty = builder.add_type(MirType::F128);
    let ptr_ty = builder.add_type(MirType::Pointer { pointee: i32_ty });

    // Function with Body
    let func_id = builder.define_function(
        NameId::new("test_func"),
        vec![i32_ty],
        void_ty,
        false,
    );
    builder.set_current_function(func_id);

    let entry_block = builder.create_block();
    builder.set_function_entry_block(func_id, entry_block);
    builder.set_current_block(entry_block);

    // Locals
    let loc_i32 = builder.create_local(Some(NameId::new("loc_i32")), i32_ty, false);
    let loc_f32 = builder.create_local(Some(NameId::new("loc_f32")), f32_ty, false);
    let loc_ptr = builder.create_local(Some(NameId::new("loc_ptr")), ptr_ty, false);

    // Constants
    let const_null = builder.create_constant(ptr_ty, ConstValueKind::Null);
    let const_zero = builder.create_constant(i32_ty, ConstValueKind::Zero);
    let const_func = builder.create_constant(ptr_ty, ConstValueKind::FunctionAddress(func_id));

    // Statements: Assign const null (to use const_null)
    builder.add_statement(MirStmt::Assign(Place::Local(loc_ptr), Rvalue::Use(Operand::Constant(const_null))));

    // Statements: Alloc/Dealloc
    builder.add_statement(MirStmt::Alloc(Place::Local(loc_i32), i32_ty));
    builder.add_statement(MirStmt::Dealloc(Operand::Copy(Box::new(Place::Local(loc_i32)))));

    // Statements: AtomicStore
    builder.add_statement(MirStmt::AtomicStore(
        Operand::Copy(Box::new(Place::Local(loc_ptr))),
        Operand::Constant(const_zero),
        AtomicMemOrder::SeqCst,
    ));

    // Statements: BuiltinVaStart/End/Copy
    builder.add_statement(MirStmt::BuiltinVaStart(
        Place::Local(loc_ptr),
        Operand::Constant(const_zero),
    ));
    builder.add_statement(MirStmt::BuiltinVaEnd(Place::Local(loc_ptr)));
    builder.add_statement(MirStmt::BuiltinVaCopy(
        Place::Local(loc_ptr),
        Place::Local(loc_ptr),
    ));

    // Statements: Store
    builder.add_statement(MirStmt::Store(
        Operand::Constant(const_zero),
        Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(loc_ptr)))))
    ));

    // RValues: BinaryFloatOp (Cover all variants)
    let ops = [
        BinaryFloatOp::Add, BinaryFloatOp::Sub, BinaryFloatOp::Mul, BinaryFloatOp::Div,
        BinaryFloatOp::Eq, BinaryFloatOp::Ne, BinaryFloatOp::Lt, BinaryFloatOp::Le,
        BinaryFloatOp::Gt, BinaryFloatOp::Ge,
    ];
    for op in ops {
        let rv = Rvalue::BinaryFloatOp(op, Operand::Copy(Box::new(Place::Local(loc_f32))), Operand::Copy(Box::new(Place::Local(loc_f32))));
        builder.add_statement(MirStmt::Assign(Place::Local(loc_f32), rv));
    }

    // RValues: UnaryFloatOp
    let rv_neg = Rvalue::UnaryFloatOp(UnaryFloatOp::Neg, Operand::Copy(Box::new(Place::Local(loc_f32))));
    builder.add_statement(MirStmt::Assign(Place::Local(loc_f32), rv_neg));

    // RValues: Atomic Ops
    let rv_atomic_load = Rvalue::AtomicLoad(Operand::Copy(Box::new(Place::Local(loc_ptr))), AtomicMemOrder::Relaxed);
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_atomic_load));

    let rv_atomic_xchg = Rvalue::AtomicExchange(
        Operand::Copy(Box::new(Place::Local(loc_ptr))),
        Operand::Constant(const_zero),
        AtomicMemOrder::AcqRel
    );
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_atomic_xchg));

    let rv_atomic_cmpxchg = Rvalue::AtomicCompareExchange(
        Operand::Copy(Box::new(Place::Local(loc_ptr))),
        Operand::Constant(const_zero),
        Operand::Constant(const_zero),
        true, // weak
        AtomicMemOrder::SeqCst,
        AtomicMemOrder::Acquire
    );
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_atomic_cmpxchg));

    let rv_atomic_fetch = Rvalue::AtomicFetchOp(
        BinaryIntOp::Add,
        Operand::Copy(Box::new(Place::Local(loc_ptr))),
        Operand::Constant(const_zero),
        AtomicMemOrder::Consume
    );
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_atomic_fetch));

    // RValues: BuiltinVaArg
    let rv_va_arg = Rvalue::BuiltinVaArg(Place::Local(loc_ptr), i32_ty);
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_va_arg));

    // RValues: Ptr Arithmetic
    let op_ptr = Operand::Copy(Box::new(Place::Local(loc_ptr)));
    let op_off = Operand::Constant(const_zero);

    let rv_ptr_add = Rvalue::PtrAdd(op_ptr.clone(), op_off.clone());
    builder.add_statement(MirStmt::Assign(Place::Local(loc_ptr), rv_ptr_add));

    let rv_ptr_sub = Rvalue::PtrSub(op_ptr.clone(), op_off.clone());
    builder.add_statement(MirStmt::Assign(Place::Local(loc_ptr), rv_ptr_sub));

    let rv_ptr_diff = Rvalue::PtrDiff(op_ptr.clone(), op_ptr.clone());
    builder.add_statement(MirStmt::Assign(Place::Local(loc_i32), rv_ptr_diff));

    // Terminator: Return(Some)
    builder.set_terminator(Terminator::Return(Some(Operand::Constant(const_zero))));

    // Create another block that is Unreachable (default terminator)
    let block2 = builder.create_block();
    builder.set_current_block(block2);
    // No terminator set, defaults to Unreachable

    // Globals
    let _ = builder.create_global_with_init(
        NameId::new("g_func_ptr"),
        ptr_ty,
        true,
        Some(const_func)
    );

    let program = builder.consume();

    // 1. Dump with Header
    let config_with_header = MirDumpConfig { include_header: true };
    let dumper = MirDumper::new(&program, &config_with_header);
    let output = dumper.generate_mir_dump().expect("MirDump failed");

    // Verify Header
    assert!(output.contains("; MIR Dump for Module 1"));
    assert!(output.contains("; Generated by Cendol C11 Compiler"));

    // Verify Contents
    assert!(output.contains("type %t3 = f80"));
    assert!(output.contains("type %t4 = f128"));

    assert!(output.contains("alloc i32"));
    assert!(output.contains("dealloc"));
    assert!(output.contains("atomic_store"));

    assert!(output.contains("va_start"));
    assert!(output.contains("va_end"));
    assert!(output.contains("va_copy"));

    assert!(output.contains("store const zero"));

    assert!(output.contains("fadd"));
    assert!(output.contains("fsub"));
    assert!(output.contains("fmul"));
    assert!(output.contains("fdiv"));
    assert!(output.contains("feq"));
    assert!(output.contains("fne"));
    assert!(output.contains("flt"));
    assert!(output.contains("fle"));
    assert!(output.contains("fgt"));
    assert!(output.contains("fge"));

    assert!(output.contains("fneg"));

    assert!(output.contains("atomic_load"));
    assert!(output.contains("atomic_xchg"));
    assert!(output.contains("atomic_cmpxchg"));
    assert!(output.contains("atomic_fetch_+"));

    assert!(output.contains("va_arg"));

    assert!(output.contains("ptradd"));
    assert!(output.contains("ptrsub"));
    assert!(output.contains("ptrdiff"));

    assert!(output.contains("unreachable"));
    assert!(output.contains("const test_func"));
    assert!(output.contains("const null"));
}
