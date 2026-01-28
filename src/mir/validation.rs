//! MIR Validation Pass
//!
//! This module implements a validation pass that ensures MIR is well-formed
//! and ready for code generation. The validation pass checks:
//! - All locals have types
//! - All blocks end with a Terminator
//! - No illegal operations remain
//! - MIR is Cranelift-safe

use crate::{
    mir::MirProgram,
    mir::{
        BinaryFloatOp, BinaryIntOp, CallTarget, ConstValue, ConstValueId, ConstValueKind, GlobalId, LocalId,
        MirBlockId, MirFunction, MirFunctionId, MirFunctionKind, MirModule, MirStmt, MirType, Operand, Place, Rvalue,
        Terminator, TypeId, UnaryFloatOp, UnaryIntOp,
    },
};

/// MIR Validation Error
#[derive(Debug, PartialEq, Clone)]
pub enum ValidationError {
    /// Local variable is missing a type
    LocalMissingType(LocalId),
    /// Illegal operation found in MIR
    IllegalOperation(String),
    /// Type not found in type table
    TypeNotFound(TypeId),
    /// Local not found in local table
    LocalNotFound(LocalId),
    /// Global not found in global table
    GlobalNotFound(GlobalId),
    /// Function not found in function table
    FunctionNotFound(MirFunctionId),
    /// Block not found in block table
    BlockNotFound(MirBlockId),
    /// Invalid pointer arithmetic operation
    InvalidPointerArithmetic,
    /// Invalid cast operation
    InvalidCast(TypeId, TypeId),
    /// Function call argument type mismatch
    FunctionCallArgTypeMismatch {
        func_name: String,
        arg_index: usize,
        expected_type: TypeId,
        actual_type: TypeId,
    },
    /// Constant value is out of range for its type
    ConstantValueOutOfRange {
        const_id: ConstValueId,
        value: i64,
        type_id: TypeId,
    },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::LocalMissingType(local_id) => write!(f, "Local {} is missing a type", local_id.get()),
            ValidationError::IllegalOperation(op) => write!(f, "Illegal operation: {}", op),
            ValidationError::TypeNotFound(type_id) => write!(f, "Type {} not found", type_id.get()),
            ValidationError::LocalNotFound(local_id) => write!(f, "Local {} not found", local_id.get()),
            ValidationError::GlobalNotFound(global_id) => write!(f, "Global {} not found", global_id.get()),
            ValidationError::FunctionNotFound(func_id) => write!(f, "Function {} not found", func_id.get()),
            ValidationError::BlockNotFound(block_id) => write!(f, "Block {} not found", block_id.get()),
            ValidationError::InvalidPointerArithmetic => write!(f, "Invalid pointer arithmetic operation"),
            ValidationError::InvalidCast(from, to) => {
                write!(f, "Invalid cast from type {} to type {}", from.get(), to.get())
            }
            ValidationError::FunctionCallArgTypeMismatch {
                func_name,
                arg_index,
                expected_type,
                actual_type,
            } => {
                write!(
                    f,
                    "Function '{}' argument {} type mismatch: expected type {}, got type {}",
                    func_name,
                    arg_index,
                    expected_type.get(),
                    actual_type.get()
                )
            }
            ValidationError::ConstantValueOutOfRange {
                const_id,
                value,
                type_id,
            } => {
                write!(
                    f,
                    "Constant {} value {} is out of range for type {}",
                    const_id.get(),
                    value,
                    type_id.get()
                )
            }
        }
    }
}

/// MIR Validation Pass
///
/// This pass validates that MIR is well-formed and ready for code generation.
/// It performs comprehensive checks but does not modify the MIR.
pub struct MirValidator<'a> {
    mir: &'a MirProgram,
    errors: Vec<ValidationError>,
}

impl<'a> MirValidator<'a> {
    /// Create a new MIR validator
    pub(crate) fn new(mir_program: &'a MirProgram) -> Self {
        Self {
            mir: mir_program,
            errors: Vec::new(),
        }
    }

    /// Validate a MIR module
    ///
    /// Returns Ok(()) if validation passes, or Err(Vec<ValidationError>) if errors are found
    pub(crate) fn validate(&mut self) -> Result<(), Vec<ValidationError>> {
        // eprintln!("VALIDATE: Starting validation");
        self.errors.clear();

        // Validate the module structure
        self.validate_module(&self.mir.module);

        // Validate each function
        for func_id in &self.mir.module.functions {
            if let Some(func) = self.mir.functions.get(func_id) {
                self.validate_function(func);
            } else {
                self.errors.push(ValidationError::FunctionNotFound(*func_id));
            }
        }

        // Validate each global
        for global_id in &self.mir.module.globals {
            if self.mir.globals.get(global_id).is_none() {
                self.errors.push(ValidationError::GlobalNotFound(*global_id));
            }
        }

        // Validate each type - module.types is a Vec<Type>, not HashMap<TypeId, Type>
        // So we validate that each type in the module is accessible via the types HashMap
        for (index, _) in self.mir.module.types.iter().enumerate() {
            let type_id = TypeId::new((index + 1) as u32).unwrap(); // Types are 1-indexed
            if !self.mir.types.contains_key(&type_id) {
                self.errors.push(ValidationError::TypeNotFound(type_id));
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }

    /// Validate module structure
    fn validate_module(&mut self, module: &MirModule) {
        // Module must have a valid ID
        if module.id.get() == 0 {
            self.errors
                .push(ValidationError::IllegalOperation("Module ID cannot be 0".to_string()));
        }
    }

    /// Validate that a constant value can be cast to the target type
    fn validate_constant_cast(&mut self, const_id: ConstValueId, const_value: &ConstValue, target_type_id: TypeId) {
        let Some(target_ty) = self.mir.types.get(&target_type_id) else {
            return;
        };
        let ConstValueKind::Int(value) = const_value.kind else {
            return;
        };

        let (min, max) = match target_ty {
            MirType::I8 | MirType::U8 => (-128, 255),
            MirType::I16 | MirType::U16 => (-32_768, 65_535),
            MirType::I32 | MirType::U32 => (-2_147_483_648, 4_294_967_295),
            MirType::Bool => (0, 1),
            _ => return, // No validation for other types
        };

        if value < min || value > max {
            self.errors.push(ValidationError::ConstantValueOutOfRange {
                const_id,
                value,
                type_id: target_type_id,
            });
        }
    }

    /// Validate a function
    fn validate_function(&mut self, func: &MirFunction) {
        // Function must have a valid ID
        if func.id.get() == 0 {
            self.errors
                .push(ValidationError::IllegalOperation("Function ID cannot be 0".to_string()));
        }

        // Function must have a name
        if func.name.as_str().is_empty() {
            self.errors.push(ValidationError::IllegalOperation(
                "Function name cannot be empty".to_string(),
            ));
        }

        // Function must have a valid return type
        if func.return_type.get() == 0 {
            self.errors.push(ValidationError::IllegalOperation(
                "Function return type cannot be 0".to_string(),
            ));
        } else if !self.mir.types.contains_key(&func.return_type) {
            self.errors.push(ValidationError::TypeNotFound(func.return_type));
        }

        // Validate all parameters
        for param_id in &func.params {
            if !self.mir.locals.contains_key(param_id) {
                self.errors.push(ValidationError::LocalNotFound(*param_id));
            }
        }

        // Validate all locals
        for local_id in &func.locals {
            if !self.mir.locals.contains_key(local_id) {
                self.errors.push(ValidationError::LocalNotFound(*local_id));
            }
        }

        // Validate all blocks
        for block_id in &func.blocks {
            if !self.mir.blocks.contains_key(block_id) {
                self.errors.push(ValidationError::BlockNotFound(*block_id));
            }
        }

        // Entry block must exist for defined functions
        if let Some(entry_block) = func.entry_block
            && !self.mir.blocks.contains_key(&entry_block)
        {
            self.errors.push(ValidationError::BlockNotFound(entry_block));
        }
        // Extern functions don't need entry blocks
        // Validate statements within blocks for defined functions
        if func.kind == MirFunctionKind::Defined {
            for block_id in &func.blocks {
                if let Some(block) = self.mir.blocks.get(block_id) {
                    for stmt_id in &block.statements {
                        if let Some(stmt) = self.mir.statements.get(stmt_id) {
                            self.validate_statement(stmt);
                        } else {
                            self.errors.push(ValidationError::IllegalOperation(format!(
                                "Statement {} not found",
                                stmt_id.get()
                            )));
                        }
                    }
                    self.validate_terminator(&block.terminator);
                }
            }
        }
    }

    fn validate_statement(&mut self, stmt: &MirStmt) {
        match stmt {
            MirStmt::Assign(place, rvalue) => {
                let place_ty = self.validate_place(place);
                let rval_ty = self.validate_rvalue(rvalue);
                if let (Some(from), Some(to)) = (rval_ty, place_ty)
                    && from != to
                    && !self.is_flexible_assignment(rvalue, from, to)
                    && !are_types_compatible(self.mir, from, to)
                {
                    self.errors.push(ValidationError::InvalidCast(from, to));
                }
            }
            MirStmt::Store(op, place) => {
                let op_ty = self.validate_operand(op);
                let place_ty = self.validate_place(place);
                if let (Some(from), Some(to)) = (op_ty, place_ty)
                    && from != to
                    && !are_types_compatible(self.mir, from, to)
                {
                    self.errors.push(ValidationError::InvalidCast(from, to));
                }
            }
            MirStmt::Call { target, args, dest } => {
                self.validate_call(target, args, dest);
            }
            MirStmt::Alloc(place, type_id) => {
                self.validate_place(place);
                if !self.mir.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
            }
            MirStmt::Dealloc(op) => {
                self.validate_operand(op);
            }
            MirStmt::BuiltinVaStart(ap, last) => {
                self.validate_place(ap);
                self.validate_operand(last);
            }
            MirStmt::BuiltinVaEnd(ap) => {
                self.validate_place(ap);
            }
            MirStmt::BuiltinVaCopy(dst, src) => {
                self.validate_place(dst);
                self.validate_place(src);
            }
            MirStmt::AtomicStore(ptr, val, _) => {
                self.validate_operand(ptr);
                self.validate_operand(val);
            }
        }
    }

    fn is_flexible_assignment(&self, rvalue: &Rvalue, from: TypeId, to: TypeId) -> bool {
        let is_flexible_op = match rvalue {
            Rvalue::UnaryIntOp(UnaryIntOp::LogicalNot, _) => true,
            Rvalue::BinaryIntOp(bin, ..) => matches!(
                bin,
                BinaryIntOp::Eq
                    | BinaryIntOp::Ne
                    | BinaryIntOp::Lt
                    | BinaryIntOp::Le
                    | BinaryIntOp::Gt
                    | BinaryIntOp::Ge
            ),
            Rvalue::BinaryFloatOp(bin, ..) => matches!(
                bin,
                BinaryFloatOp::Eq
                    | BinaryFloatOp::Ne
                    | BinaryFloatOp::Lt
                    | BinaryFloatOp::Le
                    | BinaryFloatOp::Gt
                    | BinaryFloatOp::Ge
            ),
            _ => false,
        };

        is_flexible_op && self.mir.get_type(from).is_int() && self.mir.get_type(to).is_int()
    }

    fn validate_call(&mut self, target: &CallTarget, args: &[Operand], dest: &Option<Place>) {
        self.validate_call_target(target);
        for a in args {
            self.validate_operand(a);
        }
        if let Some(dest_place) = dest {
            self.validate_place(dest_place);
        }

        match target {
            CallTarget::Direct(fid) => {
                if let Some(func) = self.mir.functions.get(fid) {
                    let param_types: Vec<TypeId> = func
                        .params
                        .iter()
                        .map(|p| self.mir.locals.get(p).unwrap().type_id)
                        .collect();
                    self.check_call_signature(
                        func.name.to_string(),
                        &param_types,
                        func.is_variadic,
                        func.return_type,
                        args,
                        dest,
                    );
                }
            }
            CallTarget::Indirect(op) => {
                if let Some(op_ty) = self.operand_type(op)
                    && let Some(MirType::Pointer { pointee }) = self.mir.types.get(&op_ty)
                    && let Some(MirType::Function {
                        params,
                        return_type,
                        is_variadic,
                    }) = self.mir.types.get(pointee)
                {
                    self.check_call_signature(
                        "indirect function".to_string(),
                        params,
                        *is_variadic,
                        *return_type,
                        args,
                        dest,
                    );
                }
            }
        }
    }

    fn check_call_signature(
        &mut self,
        name: String,
        params: &[TypeId],
        is_variadic: bool,
        return_type: TypeId,
        args: &[Operand],
        dest: &Option<Place>,
    ) {
        if (!is_variadic && args.len() != params.len()) || (is_variadic && args.len() < params.len()) {
            self.errors.push(ValidationError::IllegalOperation(format!(
                "Call to function {} arg count mismatch",
                name
            )));
            return;
        }

        for (i, arg) in args.iter().enumerate() {
            if i < params.len() {
                if let Some(arg_ty) = self.validate_operand(arg)
                    && arg_ty != params[i]
                {
                    self.errors.push(ValidationError::FunctionCallArgTypeMismatch {
                        func_name: name.clone(),
                        arg_index: i,
                        expected_type: params[i],
                        actual_type: arg_ty,
                    });
                }
            }
        }

        if let Some(dest_place) = dest {
            let _dest_ty = self.validate_place(dest_place);
            if let Some(MirType::Void) = self.mir.types.get(&return_type) {
                self.errors.push(ValidationError::IllegalOperation(format!(
                    "Call to void function {} with destination",
                    name
                )));
            }
        }
    }

    fn validate_place(&mut self, place: &Place) -> Option<TypeId> {
        match place {
            Place::Local(local_id) => {
                if let Some(local) = self.mir.locals.get(local_id) {
                    Some(local.type_id)
                } else {
                    self.errors.push(ValidationError::LocalNotFound(*local_id));
                    None
                }
            }
            Place::Deref(op) => {
                self.validate_operand(op);
                // try to infer pointer pointee type
                if let Some(op_ty) = self.operand_type(op) {
                    if let Some(MirType::Pointer { pointee }) = self.mir.types.get(&op_ty) {
                        Some(*pointee)
                    } else {
                        // Not a pointer - deref of non-pointer
                        self.errors.push(ValidationError::IllegalOperation(
                            "Deref of non-pointer operand".to_string(),
                        ));
                        None
                    }
                } else {
                    None
                }
            }
            Place::Global(gid) => {
                if let Some(g) = self.mir.globals.get(gid) {
                    Some(g.type_id)
                } else {
                    self.errors.push(ValidationError::GlobalNotFound(*gid));
                    None
                }
            }
            Place::StructField(base, idx) => {
                if let Some(base_ty) = self.validate_place(base) {
                    if let Some(MirType::Record { field_types, .. }) = self.mir.types.get(&base_ty) {
                        if *idx < field_types.len() {
                            Some(field_types[*idx])
                        } else {
                            self.errors.push(ValidationError::IllegalOperation(format!(
                                "Struct field index {} out of bounds",
                                idx
                            )));
                            None
                        }
                    } else {
                        self.errors.push(ValidationError::IllegalOperation(
                            "Struct field access on non-record type".to_string(),
                        ));
                        None
                    }
                } else {
                    None
                }
            }
            Place::ArrayIndex(base, _idx_op) => {
                // validate base place and index operand
                let _ = self.validate_place(base);
                // index operand may be complex; index operand validation is handled where used
                None
            }
        }
    }

    fn validate_operand(&mut self, op: &Operand) -> Option<TypeId> {
        match op {
            Operand::Copy(place) => self.validate_place(place),
            Operand::Constant(cid) => {
                if self.mir.constants.get(cid).is_none() {
                    self.errors.push(ValidationError::IllegalOperation(format!(
                        "Constant {} not found",
                        cid.get()
                    )));
                }
                None
            }
            Operand::AddressOf(place) => {
                if let Some(base_ty) = self.validate_place(place) {
                    // create or lookup a pointer type for base_ty is non-trivial; try to find existing pointer type
                    for (tid, ty) in &self.mir.types {
                        if let MirType::Pointer { pointee } = ty
                            && *pointee == base_ty
                        {
                            return Some(*tid);
                        }
                    }
                    None
                } else {
                    None
                }
            }
            Operand::Cast(type_id, inner) => {
                if !self.mir.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                // Check if casting a constant value that doesn't fit in the target type
                if let Operand::Constant(const_id) = inner.as_ref()
                    && let Some(const_value) = self.mir.constants.get(const_id)
                {
                    self.validate_constant_cast(*const_id, const_value, *type_id);
                }
                self.validate_operand(inner);
                Some(*type_id)
            }
        }
    }

    fn validate_rvalue(&mut self, r: &Rvalue) -> Option<TypeId> {
        match r {
            Rvalue::Use(op) => self.validate_operand(op),
            Rvalue::BinaryIntOp(bin, a, b) => {
                let ta = self.validate_operand(a);
                let tb = self.validate_operand(b);

                match bin {
                    BinaryIntOp::Eq
                    | BinaryIntOp::Ne
                    | BinaryIntOp::Lt
                    | BinaryIntOp::Le
                    | BinaryIntOp::Gt
                    | BinaryIntOp::Ge => self.find_bool_type(),
                    _ => {
                        if let (Some(ta), Some(tb)) = (ta, tb)
                            && ta != tb
                        {
                            // We could emit a warning or handle implicit promotions here if MIR allowed it,
                            // but MIR should be explicit. For now just return ta.
                        }
                        ta
                    }
                }
            }
            Rvalue::BinaryFloatOp(bin, a, b) => {
                let ta = self.validate_operand(a);
                let _tb = self.validate_operand(b);

                match bin {
                    BinaryFloatOp::Eq
                    | BinaryFloatOp::Ne
                    | BinaryFloatOp::Lt
                    | BinaryFloatOp::Le
                    | BinaryFloatOp::Gt
                    | BinaryFloatOp::Ge => self.find_bool_type(),
                    _ => ta,
                }
            }
            Rvalue::UnaryIntOp(u, a) => {
                let ta = self.validate_operand(a);
                match u {
                    UnaryIntOp::Neg => ta,
                    UnaryIntOp::BitwiseNot => ta,
                    UnaryIntOp::LogicalNot => self.find_bool_type(),
                }
            }
            Rvalue::UnaryFloatOp(u, a) => {
                let ta = self.validate_operand(a);
                match u {
                    UnaryFloatOp::Neg => ta,
                }
            }
            Rvalue::Cast(type_id, op) => {
                if !self.mir.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                let from_ty = self.validate_operand(op);
                if let (Some(from), true) = (from_ty, self.mir.types.contains_key(type_id)) {
                    // basic invalid cast check: disallow casts from record/array/enum/function to non-pointer/scalar types
                    if let Some(ty) = self.mir.types.get(&from)
                        && ty.is_aggregate()
                    {
                        if let Some(MirType::Pointer { .. }) = self.mir.types.get(type_id) {
                            // pointer casts allowed
                            // pointer casts allowed
                        } else {
                            let type_obj = self.mir.types.get(type_id).unwrap();
                            if type_obj.is_int() || type_obj.is_float() {
                                self.errors.push(ValidationError::InvalidCast(from, *type_id));
                            }
                        }
                    }
                }
                Some(*type_id)
            }
            Rvalue::PtrAdd(a, b) | Rvalue::PtrSub(a, b) => {
                self.validate_operand(a);
                self.validate_operand(b);
                None
            }
            Rvalue::PtrDiff(a, b) => {
                self.validate_operand(a);
                self.validate_operand(b);
                None
            }
            Rvalue::StructLiteral(fields) => {
                for (_idx, op) in fields {
                    self.validate_operand(op);
                }
                None
            }
            Rvalue::ArrayLiteral(elems) => {
                for e in elems {
                    self.validate_operand(e);
                }
                None
            }
            Rvalue::Load(op) => {
                self.validate_operand(op);
                None
            }

            Rvalue::BuiltinVaArg(ap, type_id) => {
                self.validate_place(ap);
                if !self.mir.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                Some(*type_id)
            }
            Rvalue::AtomicLoad(ptr, _) => {
                self.validate_operand(ptr);
                None
            }
            Rvalue::AtomicExchange(ptr, val, _) => {
                self.validate_operand(ptr);
                self.validate_operand(val);
                None
            }
            Rvalue::AtomicCompareExchange(ptr, expected, desired, _, _, _) => {
                self.validate_operand(ptr);
                self.validate_operand(expected);
                self.validate_operand(desired);
                None
            }
            Rvalue::AtomicFetchOp(_, ptr, val, _) => {
                self.validate_operand(ptr);
                self.validate_operand(val);
                None
            }
        }
    }

    fn validate_call_target(&mut self, target: &CallTarget) {
        match target {
            CallTarget::Direct(fid) => {
                if self.mir.functions.get(fid).is_none() {
                    self.errors.push(ValidationError::FunctionNotFound(*fid));
                }
            }
            CallTarget::Indirect(op) => {
                self.validate_operand(op);
            }
        }
    }

    fn operand_type(&mut self, op: &Operand) -> Option<TypeId> {
        self.validate_operand(op)
    }
    fn validate_terminator(&mut self, term: &Terminator) {
        match term {
            Terminator::Goto(bid) => {
                if !self.mir.blocks.contains_key(bid) {
                    self.errors.push(ValidationError::BlockNotFound(*bid));
                }
            }
            Terminator::If(cond, then_bb, else_bb) => {
                self.validate_operand(cond);
                if !self.mir.blocks.contains_key(then_bb) {
                    self.errors.push(ValidationError::BlockNotFound(*then_bb));
                }
                if !self.mir.blocks.contains_key(else_bb) {
                    self.errors.push(ValidationError::BlockNotFound(*else_bb));
                }
            }
            Terminator::Return(op) => {
                if let Some(op) = op {
                    self.validate_operand(op);
                }
            }
            Terminator::Unreachable => {}
        }
    }

    fn find_bool_type(&self) -> Option<TypeId> {
        for (id, ty) in &self.mir.types {
            if matches!(ty, MirType::Bool) {
                return Some(*id);
            }
        }
        None
    }
}

fn are_types_compatible(sema_output: &MirProgram, t1: TypeId, t2: TypeId) -> bool {
    if t1 == t2 {
        return true;
    }
    let ty1 = sema_output.types.get(&t1);
    let ty2 = sema_output.types.get(&t2);

    if let (Some(type1), Some(type2)) = (ty1, ty2) {
        match (type1, type2) {
            (MirType::Pointer { pointee: p1 }, MirType::Pointer { pointee: p2 }) => {
                are_types_compatible(sema_output, *p1, *p2)
            }
            (
                MirType::Array {
                    element: e1, size: s1, ..
                },
                MirType::Array {
                    element: e2, size: s2, ..
                },
            ) => s1 == s2 && are_types_compatible(sema_output, *e1, *e2),
            (
                MirType::Function {
                    return_type: r1,
                    params: pm1,
                    is_variadic: v1,
                },
                MirType::Function {
                    return_type: r2,
                    params: pm2,
                    is_variadic: v2,
                },
            ) => {
                if v1 != v2 {
                    return false;
                }
                if pm1.len() != pm2.len() {
                    return false;
                }
                are_types_compatible(sema_output, *r1, *r2)
                    && pm1
                        .iter()
                        .zip(pm2.iter())
                        .all(|(a, b)| are_types_compatible(sema_output, *a, *b))
            }
            _ => type1 == type2,
        }
    } else {
        false
    }
}
