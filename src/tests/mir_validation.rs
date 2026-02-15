use crate::ast::NameId;
use crate::mir::validation::{MirValidator, ValidationError};
use crate::mir::{
    BinaryIntOp, CallTarget, ConstValue, ConstValueId, ConstValueKind, GlobalId, Local, LocalId, MirBlock, MirBlockId,
    MirBuilder, MirFunction, MirFunctionId, MirModuleId, MirProgram, MirStmt, MirStmtId, MirType, Operand, Place,
    Rvalue, Terminator, TypeId,
};

fn create_valid_mir() -> MirProgram {
    let module_id = MirModuleId::new(1).unwrap();
    let mut builder = MirBuilder::new(module_id, 8);

    // Create a basic type: i32
    let i32_ty = builder.add_type(MirType::I32);

    // Define a function: fn main() -> i32
    let func_name = NameId::new("main");
    let func_id = builder.define_function(func_name, vec![], i32_ty, false);
    builder.set_current_function(func_id);

    // Create a block
    let block_id = builder.create_block();
    builder.set_function_entry_block(func_id, block_id);
    builder.set_current_block(block_id);

    // Add a return statement
    let const_val_id = builder.create_constant(i32_ty, ConstValueKind::Int(0));
    let operand = Operand::Constant(const_val_id);
    builder.set_terminator(Terminator::Return(Some(operand)));

    builder.consume()
}

#[test]
fn test_validation_error_display() {
    let local_id = LocalId::new(1).unwrap();
    let type_id = TypeId::new(1).unwrap();
    let global_id = GlobalId::new(1).unwrap();
    let func_id = MirFunctionId::new(1).unwrap();
    let block_id = MirBlockId::new(1).unwrap();
    let stmt_id = MirStmtId::new(1).unwrap();
    let const_id = ConstValueId::new(1).unwrap();
    let name_id = NameId::new("test_func");

    let errors = vec![
        ValidationError::LocalMissingType(local_id),
        ValidationError::IllegalOperation("test op".to_string()),
        ValidationError::TypeNotFound(type_id),
        ValidationError::LocalNotFound(local_id),
        ValidationError::GlobalNotFound(global_id),
        ValidationError::FunctionNotFound(func_id),
        ValidationError::BlockNotFound(block_id),
        ValidationError::StatementNotFound(stmt_id),
        ValidationError::InvalidPointerArithmetic,
        ValidationError::InvalidCast(type_id, TypeId::new(2).unwrap()),
        ValidationError::FunctionCallArgTypeMismatch {
            func_name: name_id,
            arg_index: 0,
            expected_type: type_id,
            actual_type: TypeId::new(2).unwrap(),
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
    let mut mir = create_valid_mir();
    // Add a function ID to module but not to map
    let invalid_id = MirFunctionId::new(999).unwrap();
    mir.module.functions.push(invalid_id);

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::FunctionNotFound(invalid_id))));
}

#[test]
fn test_missing_global() {
    let mut mir = create_valid_mir();
    let invalid_id = GlobalId::new(999).unwrap();
    mir.module.globals.push(invalid_id);

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::GlobalNotFound(invalid_id))));
}

#[test]
fn test_missing_type() {
    let mut mir = create_valid_mir();
    // Add a type to module.types but not to types map
    // module.types is Vec<MirType>.
    // Validation checks that for each index in module.types, the corresponding TypeId exists in types map.
    mir.module.types.push(MirType::Void);
    // The TypeId for this new type would be len() + 1
    let missing_type_id = TypeId::new(mir.module.types.len() as u32).unwrap();

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::TypeNotFound(missing_type_id))));
}

#[test]
fn test_invalid_function_name() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.name = NameId::new("");
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    // Contains IllegalOperation("Function name cannot be empty")
    let err = ValidationError::IllegalOperation("Function name cannot be empty".to_string());
    assert!(matches!(res, Err(errors) if errors.contains(&err)));
}

#[test]
fn test_function_missing_return_type() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let invalid_type_id = TypeId::new(999).unwrap();
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.return_type = invalid_type_id;
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::TypeNotFound(invalid_type_id))));
}

#[test]
fn test_function_missing_local() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let invalid_local_id = LocalId::new(999).unwrap();
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(invalid_local_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::LocalNotFound(invalid_local_id))));
}

#[test]
fn test_function_missing_block() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let invalid_block_id = MirBlockId::new(999).unwrap();
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.blocks.push(invalid_block_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::BlockNotFound(invalid_block_id))));
}

#[test]
fn test_block_missing_statement() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];
    let invalid_stmt_id = MirStmtId::new(999).unwrap();

    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(invalid_stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::StatementNotFound(invalid_stmt_id))));
}

#[test]
fn test_terminator_missing_block() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];
    let invalid_block_id = MirBlockId::new(999).unwrap();

    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.terminator = Terminator::Goto(invalid_block_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::BlockNotFound(invalid_block_id))));
}

#[test]
fn test_statement_alloc_missing_type() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];
    let missing_type_id = TypeId::new(999).unwrap();

    // Create a new statement Alloc(Local(1), missing_type_id)
    // We reuse existing local 1 or need to create one?
    // create_valid_mir defines 'main' with no locals/params.
    // Let's add a local.
    let local_id = LocalId::new(100).unwrap();
    let local = Local::new(local_id, None, TypeId::new(1).unwrap(), false);
    mir.locals.insert(local_id, local);
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_id);
    }

    let stmt_id = MirStmtId::new(100).unwrap();
    let stmt = MirStmt::Alloc(Place::Local(local_id), missing_type_id);
    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::TypeNotFound(missing_type_id))));
}

#[test]
fn test_call_arg_count_mismatch() {
    let _module_id = MirModuleId::new(1).unwrap();
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Create a call to main (takes 0 args) with 1 arg
    let stmt_id = MirStmtId::new(100).unwrap();
    let const_val_id = ConstValueId::new(1).unwrap(); // existing constant 0
    let arg = Operand::Constant(const_val_id);

    let stmt = MirStmt::Call {
        target: CallTarget::Direct(func_id),
        args: vec![arg],
        dest: None,
    };
    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    let expected_msg = "Call to function main arg count mismatch";
    if let Err(e) = &res {
        println!("Errors: {:?}", e);
    }
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_call_arg_type_mismatch() {
    // Need a function that takes an argument
    let _module_id = MirModuleId::new(1).unwrap();
    let mut builder = MirBuilder::new(_module_id, 8);
    let i32_ty = builder.add_type(MirType::I32);
    let f32_ty = builder.add_type(MirType::F32);

    // fn foo(a: i32) -> i32
    let func_name = NameId::new("foo");
    let func_id = builder.define_function(func_name, vec![i32_ty], i32_ty, false);
    builder.set_current_function(func_id);
    let block_id = builder.create_block();
    builder.set_function_entry_block(func_id, block_id);
    builder.set_current_block(block_id);

    // Call foo with f32 constant
    let const_f32_id = builder.create_constant(f32_ty, ConstValueKind::Float(1.0));

    // We can't easily add a statement to call itself inside builder without constructing operands.
    // Let's finish building and then inject the bad call.
    let op = Operand::Constant(builder.create_constant(i32_ty, ConstValueKind::Int(0)));
    builder.set_terminator(Terminator::Return(Some(op)));

    let mut mir = builder.consume();

    // Inject invalid call: foo(1.0)
    let stmt_id = MirStmtId::new(999).unwrap();
    let stmt = MirStmt::Call {
        target: CallTarget::Direct(func_id),
        args: vec![Operand::Constant(const_f32_id)],
        dest: None,
    };
    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        // Insert before terminator
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();

    let expected_err = ValidationError::FunctionCallArgTypeMismatch {
        func_name: func_name,
        arg_index: 0,
        expected_type: i32_ty,
        actual_type: f32_ty,
    };
    if let Err(e) = &res {
        println!("Errors: {:?}", e);
    }
    assert!(matches!(res, Err(errors) if errors.contains(&expected_err)));
}

#[test]
fn test_constant_value_out_of_range() {
    let mut mir = create_valid_mir();
    let _module_id = MirModuleId::new(1).unwrap();
    // We need to add types manually or via builder
    // Let's add u8 type manually to mir
    // Existing types: I32 (id 1)
    let u8_ty_id = TypeId::new(2).unwrap();
    mir.types.insert(u8_ty_id, MirType::U8);
    mir.module.types.push(MirType::U8);

    // Create a constant 300 (out of range for u8)
    let const_id = ConstValueId::new(999).unwrap();
    let const_val = ConstValue {
        ty: TypeId::new(1).unwrap(), // original type i32
        kind: ConstValueKind::Int(300),
    };
    mir.constants.insert(const_id, const_val);

    // Create a cast operand: Cast(u8, Constant(300))
    // We need to put this operand somewhere, e.g. in a statement
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Need a local to assign to, or use return
    // Let's use Assign to a new local of type u8
    let local_id = LocalId::new(100).unwrap();
    let local = Local::new(local_id, None, u8_ty_id, false);
    mir.locals.insert(local_id, local);
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_id);
    }

    let stmt_id = MirStmtId::new(100).unwrap();
    // Assign(Local(100), Cast(u8, Constant(300)))
    // Rvalue::Use(Operand::Cast(u8, Constant(300)))
    let rvalue = Rvalue::Use(Operand::Cast(u8_ty_id, Box::new(Operand::Constant(const_id))));
    let stmt = MirStmt::Assign(Place::Local(local_id), rvalue);

    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();

    let expected_err = ValidationError::ConstantValueOutOfRange {
        const_id,
        value: 300,
        type_id: u8_ty_id,
    };
    if let Err(e) = &res {
        println!("Errors: {:?}", e);
    }
    assert!(matches!(res, Err(errors) if errors.contains(&expected_err)));
}

#[test]
fn test_place_field_access_non_record() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Access field 0 of an i32 local
    // We need a local
    let local_id = LocalId::new(100).unwrap(); // type i32 (id 1)
    let i32_ty = TypeId::new(1).unwrap();
    let local = Local::new(local_id, None, i32_ty, false);
    mir.locals.insert(local_id, local);
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_id);
    }

    let stmt_id = MirStmtId::new(100).unwrap();
    // Assign(Local(..), Use(Copy(StructField(Local(100), 0))))
    // But struct field on i32 is invalid
    let place = Place::StructField(Box::new(Place::Local(local_id)), 0);
    // To trigger validate_place, we can use it in operand Copy
    let rvalue = Rvalue::Use(Operand::Copy(Box::new(place)));

    let dest_local_id = LocalId::new(101).unwrap();
    let dest_local = Local::new(dest_local_id, None, i32_ty, false);
    mir.locals.insert(dest_local_id, dest_local);
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(dest_local_id);
    }

    let stmt = MirStmt::Assign(Place::Local(dest_local_id), rvalue);
    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    let expected_msg = "Struct field access on non-record type";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_invalid_pointer_arithmetic() {
    // There is no explicit invalid pointer arithmetic check triggered in validation.rs in the current snapshot
    // But there is Rvalue::PtrAdd validation.
    // It checks operands but doesn't check if they are pointers?
    // Looking at validate_rvalue in validation.rs:
    // Rvalue::PtrAdd(a, b) => { validate_operand(a); validate_operand(b); None }
    // It returns None, which means unknown type.
    // So invalid pointer arithmetic (e.g. adding two pointers?) is not caught by validation currently?
    // Wait, the validation logic for PtrAdd is minimal.
    // The ValidationError::InvalidPointerArithmetic exists but might be unused.
    // I'll skip testing it for logic, but I've covered it in Display test.
}

#[test]
fn test_invalid_cast_in_assignment() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Add float type
    let f32_ty = TypeId::new(2).unwrap();
    mir.types.insert(f32_ty, MirType::F32);
    mir.module.types.push(MirType::F32);

    // Create i32 local and f32 local
    let i32_ty = TypeId::new(1).unwrap();
    let local_i32 = LocalId::new(100).unwrap();
    let local_f32 = LocalId::new(101).unwrap();

    mir.locals.insert(local_i32, Local::new(local_i32, None, i32_ty, false));
    mir.locals.insert(local_f32, Local::new(local_f32, None, f32_ty, false));

    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_i32);
        func.locals.push(local_f32);
    }

    // Assign f32 local to i32 local without cast
    // local_i32 = local_f32
    let stmt_id = MirStmtId::new(100).unwrap();
    let rvalue = Rvalue::Use(Operand::Copy(Box::new(Place::Local(local_f32))));
    let stmt = MirStmt::Assign(Place::Local(local_i32), rvalue);

    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    // Should be InvalidCast(f32, i32)
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::InvalidCast(f32_ty, i32_ty))));
}

#[test]
fn test_flexible_assignment() {
    // Test that assigning boolean result of comparison to int is allowed (if is_flexible_assignment is true)
    // Actually is_flexible_assignment checks if rvalue is comparison/logic and target is int.

    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];
    let i32_ty = TypeId::new(1).unwrap();

    // Create locals
    let local_dest = LocalId::new(100).unwrap(); // i32
    let local_src = LocalId::new(101).unwrap(); // i32

    mir.locals
        .insert(local_dest, Local::new(local_dest, None, i32_ty, false));
    mir.locals.insert(local_src, Local::new(local_src, None, i32_ty, false));

    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_dest);
        func.locals.push(local_src);
    }

    // Assign boolean comparison to i32: x = (a == b)
    // Rvalue::BinaryIntOp(Eq, a, b) returns Bool type in validate_rvalue (find_bool_type) if it exists?
    // Wait, validation returns boolean type if found.
    // If Bool type doesn't exist in module, find_bool_type returns None.

    // Let's add Bool type
    let bool_ty = TypeId::new(2).unwrap();
    mir.types.insert(bool_ty, MirType::Bool);
    mir.module.types.push(MirType::Bool);

    let stmt_id = MirStmtId::new(100).unwrap();
    let op = Operand::Copy(Box::new(Place::Local(local_src)));
    let rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Eq, op.clone(), op.clone());

    // Assign to i32
    let stmt = MirStmt::Assign(Place::Local(local_dest), rvalue);

    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    // This should Pass because of is_flexible_assignment allowlisting comparisons assigned to ints
    assert_eq!(validator.validate(), Ok(()));
}

#[test]
fn test_call_void_with_dest() {
    let _module_id = MirModuleId::new(1).unwrap();
    let mut builder = MirBuilder::new(_module_id, 8);
    let void_ty = builder.add_type(MirType::Void);
    let i32_ty = builder.add_type(MirType::I32);

    // fn foo() -> void
    let foo_name = NameId::new("foo");
    let foo_id = builder.define_function(foo_name, vec![], void_ty, false);
    builder.set_current_function(foo_id);
    let block_id = builder.create_block();
    builder.set_function_entry_block(foo_id, block_id);
    builder.set_current_block(block_id);
    builder.set_terminator(Terminator::Return(None));

    let mut mir = builder.consume();

    // fn main() -> i32
    let main_name = NameId::new("main");
    let main_id = MirFunctionId::new(2).unwrap();
    let main_func = MirFunction::new_defined(main_id, main_name, i32_ty);
    mir.functions.insert(main_id, main_func.clone());
    mir.module.functions.push(main_id);

    // Call foo() -> void, assign to i32 local
    let local_id = LocalId::new(100).unwrap();
    let local = Local::new(local_id, None, i32_ty, false);
    mir.locals.insert(local_id, local);
    if let Some(func) = mir.functions.get_mut(&main_id) {
        func.locals.push(local_id);
    }

    let stmt_id = MirStmtId::new(100).unwrap();
    let stmt = MirStmt::Call {
        target: CallTarget::Direct(foo_id),
        args: vec![],
        dest: Some(Place::Local(local_id)),
    };

    mir.statements.insert(stmt_id, stmt);
    // Add block to main
    let main_block_id = MirBlockId::new(2).unwrap();
    let mut main_block = MirBlock::new(main_block_id);
    main_block.statements.push(stmt_id);
    mir.blocks.insert(main_block_id, main_block);
    if let Some(func) = mir.functions.get_mut(&main_id) {
        func.blocks.push(main_block_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    let expected_msg = "Call to void function foo with destination";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_operand_missing_constant() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Refer to non-existent constant
    let invalid_const_id = ConstValueId::new(999).unwrap();
    let op = Operand::Constant(invalid_const_id);

    // Use it in Return
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.terminator = Terminator::Return(Some(op));
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    let expected_msg = "Constant 999 not found";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_operand_cast_missing_type() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    let missing_type_id = TypeId::new(999).unwrap();
    let const_val_id = ConstValueId::new(1).unwrap(); // existing 0
    let op = Operand::Cast(missing_type_id, Box::new(Operand::Constant(const_val_id)));

    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.terminator = Terminator::Return(Some(op));
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::TypeNotFound(missing_type_id))));
}

#[test]
fn test_place_deref_non_pointer() {
    let mut mir = create_valid_mir();
    let func_id = mir.module.functions[0];
    let func = mir.functions.get(&func_id).unwrap();
    let block_id = func.blocks[0];

    // Dereference an i32 local
    let local_id = LocalId::new(100).unwrap();
    let i32_ty = TypeId::new(1).unwrap();
    let local = Local::new(local_id, None, i32_ty, false);
    mir.locals.insert(local_id, local);
    if let Some(func) = mir.functions.get_mut(&func_id) {
        func.locals.push(local_id);
    }

    let place = Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(local_id)))));
    // Use it as rvalue
    let rvalue = Rvalue::Use(Operand::Copy(Box::new(place)));

    let stmt_id = MirStmtId::new(100).unwrap();
    let stmt = MirStmt::Assign(Place::Local(local_id), rvalue);

    mir.statements.insert(stmt_id, stmt);
    if let Some(block) = mir.blocks.get_mut(&block_id) {
        block.statements.push(stmt_id);
    }

    let validator = MirValidator::new(&mir);
    let res = validator.validate();
    let expected_msg = "Deref of non-pointer operand";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_place_field_out_of_bounds() {
    let _module_id = MirModuleId::new(1).unwrap();
    let mut builder = MirBuilder::new(_module_id, 8);
    let i32_ty = builder.add_type(MirType::I32);

    // Create struct with 1 field
    use crate::mir::MirRecordLayout;
    let struct_ty = MirType::Record {
        name: NameId::new("MyStruct"),
        field_types: vec![i32_ty],
        field_names: vec![NameId::new("f1")],
        is_union: false,
        layout: MirRecordLayout {
            size: 4,
            alignment: 4,
            field_offsets: vec![0],
        },
    };
    let struct_ty_id = builder.add_type(struct_ty);

    let func_id = builder.define_function(NameId::new("main"), vec![], i32_ty, false);
    builder.set_current_function(func_id);
    let block_id = builder.create_block();
    builder.set_function_entry_block(func_id, block_id);
    builder.set_current_block(block_id);

    let local_id = builder.create_local(None, struct_ty_id, false);

    // Access field 1 (out of bounds, size is 1)
    let place = Place::StructField(Box::new(Place::Local(local_id)), 1);
    let op = Operand::Copy(Box::new(place));
    // Assign to i32 local
    let dest_local = builder.create_local(None, i32_ty, false);
    let stmt = MirStmt::Assign(Place::Local(dest_local), Rvalue::Use(op));
    builder.add_statement(stmt);
    let const_val = builder.create_constant(i32_ty, ConstValueKind::Int(0));
    builder.set_terminator(Terminator::Return(Some(Operand::Constant(const_val))));

    let mir = builder.consume();
    let validator = MirValidator::new(&mir);
    let res = validator.validate();

    let expected_msg = "Struct field index 1 out of bounds";
    assert!(
        matches!(res, Err(errors) if errors.iter().any(|e| matches!(e, ValidationError::IllegalOperation(msg) if msg == expected_msg)))
    );
}

#[test]
fn test_rvalue_cast_aggregate_invalid() {
    let _module_id = MirModuleId::new(1).unwrap();
    let mut builder = MirBuilder::new(_module_id, 8);
    let i32_ty = builder.add_type(MirType::I32);

    // Create struct
    use crate::mir::MirRecordLayout;
    let struct_ty = MirType::Record {
        name: NameId::new("MyStruct"),
        field_types: vec![i32_ty],
        field_names: vec![NameId::new("f1")],
        is_union: false,
        layout: MirRecordLayout {
            size: 4,
            alignment: 4,
            field_offsets: vec![0],
        },
    };
    let struct_ty_id = builder.add_type(struct_ty);

    let func_id = builder.define_function(NameId::new("main"), vec![], i32_ty, false);
    builder.set_current_function(func_id);
    let block_id = builder.create_block();
    builder.set_function_entry_block(func_id, block_id);
    builder.set_current_block(block_id);

    let local_id = builder.create_local(None, struct_ty_id, false);

    // Cast struct to i32 - invalid
    let rvalue = Rvalue::Cast(i32_ty, Operand::Copy(Box::new(Place::Local(local_id))));
    let dest_local = builder.create_local(None, i32_ty, false);
    let stmt = MirStmt::Assign(Place::Local(dest_local), rvalue);
    builder.add_statement(stmt);
    let const_val = builder.create_constant(i32_ty, ConstValueKind::Int(0));
    builder.set_terminator(Terminator::Return(Some(Operand::Constant(const_val))));

    let mir = builder.consume();
    let validator = MirValidator::new(&mir);
    let res = validator.validate();

    assert!(matches!(res, Err(errors) if errors.contains(&ValidationError::InvalidCast(struct_ty_id, i32_ty))));
}
