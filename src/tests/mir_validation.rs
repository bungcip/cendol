use crate::ast::NameId;
use crate::mir::validation::{MirValidator, ValidationError};
use crate::mir::{
    BinaryIntOp, CallTarget, ConstValue, ConstValueId, ConstValueKind, GlobalId, Local, LocalId, MirBlockId,
    MirBuilder, MirFieldLayout, MirFunction, MirFunctionId, MirProgram, MirRecordLayout, MirStmt, MirStmtId, MirType,
    Operand, Place, Rvalue, Terminator, TypeId,
};

fn create_valid_mir() -> MirProgram {
    let mut builder = MirBuilder::new(8);

    // Create a basic type: i32
    let i32_ty = builder.add_type(MirType::I32);

    // Define a function: fn main() -> i32
    let func_name = NameId::new("main");
    let func_id = builder.define_function(func_name, vec![], i32_ty, false, crate::mir::MirLinkage::External);

    let const_val_id = builder.create_constant(i32_ty, ConstValueKind::Int(0));
    let operand = Operand::Constant(const_val_id);

    {
        let mut fb = builder.build_function(func_id, None);
        let block_id = fb.create_block();
        fb.builder.set_function_entry_block(func_id, block_id);
        fb.current_block = Some(block_id);
        fb.set_terminator(Terminator::Return(Some(operand)));
    }

    builder.consume()
}

fn validate(mir: &MirProgram) -> Result<(), Vec<ValidationError>> {
    MirValidator::new(mir).validate()
}

fn check_err(expected: ValidationError, f: impl FnOnce(&mut MirProgram)) {
    let mut mir = create_valid_mir();
    f(&mut mir);
    let res = validate(&mir);
    assert!(
        matches!(&res, Err(errors) if errors.contains(&expected)),
        "Expected error {:?}, but found {:?}",
        expected,
        res
    );
}

fn inject_stmt(mir: &mut MirProgram, stmt: MirStmt) -> MirStmtId {
    let func_id = mir.module.functions[0];
    let block_id = mir.functions[func_id.index()].blocks[0];
    mir.statements.push(stmt);
    let stmt_id = MirStmtId::new(mir.statements.len() as u32).unwrap();
    mir.blocks[block_id.index()].statements.push(stmt_id);
    stmt_id
}

fn add_type(mir: &mut MirProgram, ty: MirType) -> TypeId {
    mir.types.push(ty.clone());
    mir.module.types.push(ty);
    TypeId::new(mir.types.len() as u32).unwrap()
}

#[test]
fn test_validation_error_display() {
    let local_id = LocalId::new(1).unwrap();
    let type_id = TypeId::new(1).unwrap();
    let type_id2 = TypeId::new(2).unwrap();
    let global_id = GlobalId::new(1).unwrap();
    let func_id = MirFunctionId::new(1).unwrap();
    let block_id = MirBlockId::new(1).unwrap();
    let stmt_id = MirStmtId::new(1).unwrap();
    let const_id = ConstValueId::new(1).unwrap();
    let name_id = NameId::new("test_func");

    let err = ValidationError::InvalidCast(type_id, type_id2);

    // Without guard, formats using raw integer IDs
    assert_eq!(format!("{}", err), "Invalid cast from type 1 to type 2");

    // With guard, formats using type names recursively
    let types = vec![MirType::I32, MirType::Pointer { pointee: type_id }];
    {
        let _guard = crate::mir::ActiveTypesGuard::new(&types);
        assert_eq!(format!("{}", err), "Invalid cast from type i32 to type *i32");
    }

    let errors = vec![
        ValidationError::IllegalOperation("test op".to_string()),
        ValidationError::TypeNotFound(type_id),
        ValidationError::LocalNotFound(local_id),
        ValidationError::GlobalNotFound(global_id),
        ValidationError::FunctionNotFound(func_id),
        ValidationError::BlockNotFound(block_id),
        ValidationError::StatementNotFound(stmt_id),
        ValidationError::InvalidCast(type_id, type_id2),
        ValidationError::FunctionCallArgTypeMismatch {
            func_name: name_id,
            arg_index: 0,
            expected_type: type_id,
            actual_type: type_id2,
        },
        ValidationError::ConstantValueOutOfRange {
            const_id,
            value: 100,
            type_id,
        },
    ];

    for err in errors {
        // Just verify it doesn't panic and produces some string
        let s = format!("{}", err);
        assert!(!s.is_empty());
    }
}

#[test]
fn test_valid_mir() {
    let mir = create_valid_mir();
    let validator = MirValidator::new(&mir);
    assert_eq!(validator.validate(), Ok(()));
}

#[test]
fn test_missing_function() {
    let invalid_id = MirFunctionId::new(999).unwrap();
    check_err(ValidationError::FunctionNotFound(invalid_id), |m| {
        m.module.functions.push(invalid_id);
    });
}

#[test]
fn test_missing_global() {
    let invalid_id = GlobalId::new(999).unwrap();
    check_err(ValidationError::GlobalNotFound(invalid_id), |m| {
        m.module.globals.push(invalid_id);
    });
}

#[test]
fn test_missing_type() {
    check_err(ValidationError::TypeNotFound(TypeId::new(2).unwrap()), |m| {
        m.module.types.push(MirType::Void);
    });
}

#[test]
fn test_invalid_function_name() {
    check_err(
        ValidationError::IllegalOperation("Function name cannot be empty".to_string()),
        |m| {
            let func_id = m.module.functions[0];
            m.functions[func_id.index()].name = NameId::new("");
        },
    );
}

#[test]
fn test_function_missing_return_type() {
    let invalid_type_id = TypeId::new(999).unwrap();
    check_err(ValidationError::TypeNotFound(invalid_type_id), |m| {
        let func_id = m.module.functions[0];
        m.functions[func_id.index()].return_type = invalid_type_id;
    });
}

#[test]
fn test_function_missing_local() {
    let invalid_local_id = LocalId::new(999).unwrap();
    check_err(ValidationError::LocalNotFound(invalid_local_id), |m| {
        let func_id = m.module.functions[0];
        m.functions[func_id.index()].locals.push(invalid_local_id);
    });
}

#[test]
fn test_function_missing_block() {
    let invalid_block_id = MirBlockId::new(999).unwrap();
    check_err(ValidationError::BlockNotFound(invalid_block_id), |m| {
        let func_id = m.module.functions[0];
        m.functions[func_id.index()].blocks.push(invalid_block_id);
    });
}

#[test]
fn test_block_missing_statement() {
    let invalid_stmt_id = MirStmtId::new(999).unwrap();
    check_err(ValidationError::StatementNotFound(invalid_stmt_id), |m| {
        let block_id = m.functions[m.module.functions[0].index()].blocks[0];
        m.blocks[block_id.index()].statements.push(invalid_stmt_id);
    });
}

#[test]
fn test_terminator_missing_block() {
    let invalid_block_id = MirBlockId::new(999).unwrap();
    check_err(ValidationError::BlockNotFound(invalid_block_id), |m| {
        let block_id = m.functions[m.module.functions[0].index()].blocks[0];
        m.blocks[block_id.index()].terminator = Terminator::Goto(invalid_block_id);
    });
}

#[test]
fn test_call_arg_count_mismatch() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let f32_ty = add_type(&mut mir, MirType::F32);

    let func_name = NameId::new("foo");
    let foo_id = MirFunctionId::new(mir.functions.len() as u32 + 1).unwrap();
    let mut foo = MirFunction::new_defined(func_name, i32_ty, crate::mir::MirLinkage::External);
    let param_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(Some(NameId::new("a")), i32_ty, true));
    foo.params.push(param_id);
    mir.functions.push(foo);
    mir.module.functions.push(foo_id);

    let const_f32_id = ConstValueId::new(mir.constants.len() as u32 + 1).unwrap();
    mir.constants.push(ConstValue {
        ty: f32_ty,
        kind: ConstValueKind::Float(1.0),
    });

    inject_stmt(
        &mut mir,
        MirStmt::Call {
            target: CallTarget::Direct(foo_id),
            args: vec![Operand::Constant(const_f32_id)],
            dest: None,
        },
    );

    let res = validate(&mir);
    let expected_err = ValidationError::FunctionCallArgTypeMismatch {
        func_name,
        arg_index: 0,
        expected_type: i32_ty,
        actual_type: f32_ty,
    };
    assert!(matches!(res, Err(errors) if errors.contains(&expected_err)));
}

#[test]
fn test_constant_value_out_of_range() {
    let mut mir = create_valid_mir();
    let u8_ty = add_type(&mut mir, MirType::U8);
    let i32_ty = TypeId::new(1).unwrap();

    let const_id = ConstValueId::new(mir.constants.len() as u32 + 1).unwrap();
    mir.constants.push(ConstValue {
        ty: i32_ty,
        kind: ConstValueKind::Int(300),
    });

    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, u8_ty, false));
    mir.functions[mir.module.functions[0].index()].locals.push(local_id);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(local_id),
            Rvalue::Use(Operand::Cast(u8_ty, Box::new(Operand::Constant(const_id)))),
        ),
    );

    let res = validate(&mir);
    let expected_err = ValidationError::ConstantValueOutOfRange {
        const_id,
        value: 300,
        type_id: u8_ty,
    };
    assert!(matches!(res, Err(errors) if errors.contains(&expected_err)));
}

#[test]
fn test_struct_field_access_on_non_record() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    mir.functions[mir.module.functions[0].index()].locals.push(local_id);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(local_id),
            Rvalue::Use(Operand::Copy(Box::new(Place::StructField(
                Box::new(Place::Local(local_id)),
                0,
                None,
            )))),
        ),
    );

    let res = validate(&mir);
    let expected_msg = "Struct field access on non-record type";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_invalid_cast_in_assignment() {
    let mut mir = create_valid_mir();
    let f32_ty = add_type(&mut mir, MirType::F32);
    let i32_ty = TypeId::new(1).unwrap();

    let local_i32 = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    let local_f32 = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, f32_ty, false));

    mir.functions[mir.module.functions[0].index()]
        .locals
        .extend([local_i32, local_f32]);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(local_i32),
            Rvalue::Use(Operand::Copy(Box::new(Place::Local(local_f32)))),
        ),
    );

    assert!(matches!(validate(&mir), Err(errors) if errors.contains(&ValidationError::InvalidCast(f32_ty, i32_ty))));
}

#[test]
fn test_flexible_assignment() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let _bool_ty = add_type(&mut mir, MirType::Bool);

    let local_dest = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    let local_src = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));

    mir.functions[mir.module.functions[0].index()]
        .locals
        .extend([local_dest, local_src]);

    let op = Operand::Copy(Box::new(Place::Local(local_src)));
    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(local_dest),
            Rvalue::BinaryIntOp(BinaryIntOp::Eq, op.clone(), op),
        ),
    );

    assert_eq!(validate(&mir), Ok(()));
}

#[test]
fn test_call_void_with_dest() {
    let mut mir = create_valid_mir();
    let void_ty = add_type(&mut mir, MirType::Void);
    let i32_ty = TypeId::new(1).unwrap();

    let foo_name = NameId::new("foo");
    let foo_id = MirFunctionId::new(mir.functions.len() as u32 + 1).unwrap();
    mir.functions.push(MirFunction::new_defined(
        foo_name,
        void_ty,
        crate::mir::MirLinkage::External,
    ));
    mir.module.functions.push(foo_id);

    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    mir.functions[mir.module.functions[0].index()].locals.push(local_id);

    inject_stmt(
        &mut mir,
        MirStmt::Call {
            target: CallTarget::Direct(foo_id),
            args: vec![],
            dest: Some(Place::Local(local_id)),
        },
    );

    let res = validate(&mir);
    let expected_msg = "Call to void function foo with destination";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_operand_missing_constant() {
    let invalid_id = ConstValueId::new(999).unwrap();
    check_err(
        ValidationError::IllegalOperation("Constant 999 not found".to_string()),
        |m| {
            let block_id = m.functions[m.module.functions[0].index()].blocks[0];
            m.blocks[block_id.index()].terminator = Terminator::Return(Some(Operand::Constant(invalid_id)));
        },
    );
}

#[test]
fn test_operand_cast_missing_type() {
    let missing_type_id = TypeId::new(999).unwrap();
    check_err(ValidationError::TypeNotFound(missing_type_id), |m| {
        let block_id = m.functions[m.module.functions[0].index()].blocks[0];
        let const_val_id = ConstValueId::new(1).unwrap();
        let op = Operand::Cast(missing_type_id, Box::new(Operand::Constant(const_val_id)));
        m.blocks[block_id.index()].terminator = Terminator::Return(Some(op));
    });
}

#[test]
fn test_place_deref_non_pointer() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    mir.functions[mir.module.functions[0].index()].locals.push(local_id);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(local_id),
            Rvalue::Use(Operand::Copy(Box::new(Place::Deref(Box::new(Operand::Copy(
                Box::new(Place::Local(local_id)),
            )))))),
        ),
    );

    let res = validate(&mir);
    let expected_msg = "Deref of non-pointer operand";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_place_field_out_of_bounds() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let struct_ty = MirType::Record {
        name: NameId::new("MyStruct"),
        field_types: vec![i32_ty],
        field_names: vec![NameId::new("f1")],
        is_union: false,
        layout: MirRecordLayout {
            size: 4,
            align: 4,
            fields: vec![MirFieldLayout::new(0, 4).signed(true)],
        },
    };
    let struct_ty_id = add_type(&mut mir, struct_ty);

    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, struct_ty_id, false));
    let dest_local = LocalId::new(mir.locals.len() as u32 + 2).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    mir.functions[mir.module.functions[0].index()]
        .locals
        .extend([local_id, dest_local]);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(dest_local),
            Rvalue::Use(Operand::Copy(Box::new(Place::StructField(
                Box::new(Place::Local(local_id)),
                1,
                None,
            )))),
        ),
    );

    let res = validate(&mir);
    let expected_msg = "Struct field index 1 out of bounds";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_rvalue_cast_aggregate_invalid() {
    let mut mir = create_valid_mir();
    let i32_ty = TypeId::new(1).unwrap();
    let struct_ty = MirType::Record {
        name: NameId::new("MyStruct"),
        field_types: vec![i32_ty],
        field_names: vec![NameId::new("f1")],
        is_union: false,
        layout: MirRecordLayout {
            size: 4,
            align: 4,
            fields: vec![MirFieldLayout::new(0, 4).signed(true)],
        },
    };
    let struct_ty_id = add_type(&mut mir, struct_ty);

    let local_id = LocalId::new(mir.locals.len() as u32 + 1).unwrap();
    mir.locals.push(Local::new(None, struct_ty_id, false));
    let dest_local = LocalId::new(mir.locals.len() as u32 + 2).unwrap();
    mir.locals.push(Local::new(None, i32_ty, false));
    mir.functions[mir.module.functions[0].index()]
        .locals
        .extend([local_id, dest_local]);

    inject_stmt(
        &mut mir,
        MirStmt::Assign(
            Place::Local(dest_local),
            Rvalue::Use(Operand::Cast(
                i32_ty,
                Box::new(Operand::Copy(Box::new(Place::Local(local_id)))),
            )),
        ),
    );

    assert!(
        matches!(validate(&mir), Err(errors) if errors.contains(&ValidationError::InvalidCast(struct_ty_id, i32_ty)))
    );
}
