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
        BinaryFloatOp, BinaryIntOp, CallTarget, GlobalId, LocalId, MirBlockId, MirFunction, MirFunctionId,
        MirFunctionKind, MirModule, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryFloatOp,
        UnaryIntOp,
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
        }
    }
}

/// MIR Validation Pass
///
/// This pass validates that MIR is well-formed and ready for code generation.
/// It performs comprehensive checks but does not modify the MIR.
#[derive(Default)]
pub struct MirValidator {
    errors: Vec<ValidationError>,
}

impl MirValidator {
    /// Create a new MIR validator
    pub(crate) fn new() -> Self {
        Self { errors: Vec::new() }
    }

    /// Validate a MIR module
    ///
    /// Returns Ok(()) if validation passes, or Err(Vec<ValidationError>) if errors are found
    pub(crate) fn validate(&mut self, sema_output: &MirProgram) -> Result<(), Vec<ValidationError>> {
        self.errors.clear();

        // Validate the module structure
        self.validate_module(&sema_output.module);

        // Validate each function
        for func_id in &sema_output.module.functions {
            if let Some(func) = sema_output.functions.get(func_id) {
                self.validate_function(sema_output, func);
            } else {
                self.errors.push(ValidationError::FunctionNotFound(*func_id));
            }
        }

        // Validate each global
        for global_id in &sema_output.module.globals {
            if sema_output.globals.get(global_id).is_none() {
                self.errors.push(ValidationError::GlobalNotFound(*global_id));
            }
        }

        // Validate each type - module.types is a Vec<Type>, not HashMap<TypeId, Type>
        // So we validate that each type in the module is accessible via the types HashMap
        for (index, _) in sema_output.module.types.iter().enumerate() {
            let type_id = TypeId::new((index + 1) as u32).unwrap(); // Types are 1-indexed
            if !sema_output.types.contains_key(&type_id) {
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

    /// Validate a function
    fn validate_function(&mut self, sema_output: &MirProgram, func: &MirFunction) {
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
        } else if !sema_output.types.contains_key(&func.return_type) {
            self.errors.push(ValidationError::TypeNotFound(func.return_type));
        }

        // Validate all parameters
        for param_id in &func.params {
            if !sema_output.locals.contains_key(param_id) {
                self.errors.push(ValidationError::LocalNotFound(*param_id));
            }
        }

        // Validate all locals
        for local_id in &func.locals {
            if !sema_output.locals.contains_key(local_id) {
                self.errors.push(ValidationError::LocalNotFound(*local_id));
            }
        }

        // Validate all blocks
        for block_id in &func.blocks {
            if !sema_output.blocks.contains_key(block_id) {
                self.errors.push(ValidationError::BlockNotFound(*block_id));
            }
        }

        // Entry block must exist for defined functions
        if let Some(entry_block) = func.entry_block
            && !sema_output.blocks.contains_key(&entry_block)
        {
            self.errors.push(ValidationError::BlockNotFound(entry_block));
        }
        // Extern functions don't need entry blocks
        // Validate statements within blocks for defined functions
        if func.kind == MirFunctionKind::Defined {
            for block_id in &func.blocks {
                if let Some(block) = sema_output.blocks.get(block_id) {
                    for stmt_id in &block.statements {
                        if let Some(stmt) = sema_output.statements.get(stmt_id) {
                            self.validate_statement(sema_output, stmt);
                        } else {
                            self.errors.push(ValidationError::IllegalOperation(format!(
                                "Statement {} not found",
                                stmt_id.get()
                            )));
                        }
                    }
                    self.validate_terminator(sema_output, &block.terminator);
                }
            }
        }
    }

    fn validate_statement(&mut self, sema_output: &MirProgram, stmt: &MirStmt) {
        match stmt {
            MirStmt::Assign(place, rvalue) => {
                let place_ty = self.validate_place(sema_output, place);
                let rval_ty = self.validate_rvalue(sema_output, rvalue);
                if let (Some(from), Some(to)) = (rval_ty, place_ty)
                    && from != to
                {
                    // Special case for operations that can return multiple types (bool or int)
                    let is_flexible = match rvalue {
                        Rvalue::UnaryIntOp(UnaryIntOp::LogicalNot, _) => true,
                        Rvalue::BinaryIntOp(bin, _, _) => matches!(
                            bin,
                            BinaryIntOp::Eq
                                | BinaryIntOp::Ne
                                | BinaryIntOp::Lt
                                | BinaryIntOp::Le
                                | BinaryIntOp::Gt
                                | BinaryIntOp::Ge
                        ),
                        Rvalue::BinaryFloatOp(bin, _, _) => matches!(
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

                    if is_flexible {
                        let _bool_ty = self.find_bool_type(sema_output);
                        let is_bool_or_int = |tid: TypeId| {
                            if let Some(ty) = sema_output.types.get(&tid) {
                                ty.is_int()
                            } else {
                                false
                            }
                        };

                        if is_bool_or_int(from) && is_bool_or_int(to) {
                            // Allowed for these flexible operations
                            return;
                        }
                    }

                    if !self.are_types_compatible(sema_output, from, to) {
                        self.errors.push(ValidationError::InvalidCast(from, to));
                    }
                }
            }
            MirStmt::Store(op, place) => {
                let op_ty = self.validate_operand(sema_output, op);
                let place_ty = self.validate_place(sema_output, place);
                if let (Some(from), Some(to)) = (op_ty, place_ty)
                    && from != to
                    && !self.are_types_compatible(sema_output, from, to)
                {
                    self.errors.push(ValidationError::InvalidCast(from, to));
                }
            }
            MirStmt::Call(target, args) => {
                self.validate_call_target(sema_output, target);
                for a in args {
                    self.validate_operand(sema_output, a);
                }
                // Validate argument types against function signature when possible
                match target {
                    CallTarget::Direct(fid) => {
                        if let Some(func) = sema_output.functions.get(fid) {
                            // use param locals to get their types
                            if func.params.len() != args.len() && !func.is_variadic {
                                self.errors.push(ValidationError::IllegalOperation(format!(
                                    "Call to function {} arg count mismatch",
                                    fid.get()
                                )));
                            } else {
                                for (i, arg) in args.iter().enumerate().take(func.params.len()) {
                                    let param_id = func.params[i];
                                    if let Some(param) = sema_output.locals.get(&param_id)
                                        && let Some(arg_ty) = self.validate_operand(sema_output, arg)
                                        && arg_ty != param.type_id
                                    {
                                        self.errors.push(ValidationError::FunctionCallArgTypeMismatch {
                                            func_name: func.name.to_string(),
                                            arg_index: i,
                                            expected_type: param.type_id,
                                            actual_type: arg_ty,
                                        });
                                    }
                                }
                            }
                        }
                    }
                    CallTarget::Indirect(op) => {
                        if let Some(op_ty) = self.validate_operand(sema_output, op)
                            && let Some(MirType::Pointer { pointee }) = sema_output.types.get(&op_ty)
                            && let Some(MirType::Function { params, .. }) = sema_output.types.get(pointee)
                        {
                            if params.len() != args.len() {
                                self.errors.push(ValidationError::IllegalOperation(
                                    "Indirect call argument count mismatch".to_string(),
                                ));
                            } else {
                                for (i, arg) in args.iter().enumerate() {
                                    if let Some(arg_ty) = self.validate_operand(sema_output, arg)
                                        && arg_ty != params[i]
                                    {
                                        self.errors.push(ValidationError::FunctionCallArgTypeMismatch {
                                            func_name: "indirect function".to_string(),
                                            arg_index: i,
                                            expected_type: params[i],
                                            actual_type: arg_ty,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
            MirStmt::Alloc(place, type_id) => {
                self.validate_place(sema_output, place);
                if !sema_output.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
            }
            MirStmt::Dealloc(op) => {
                self.validate_operand(sema_output, op);
            }
            MirStmt::BuiltinVaStart(ap, last) => {
                self.validate_operand(sema_output, ap);
                self.validate_operand(sema_output, last);
            }
            MirStmt::BuiltinVaEnd(ap) => {
                self.validate_operand(sema_output, ap);
            }
            MirStmt::BuiltinVaCopy(dst, src) => {
                self.validate_operand(sema_output, dst);
                self.validate_operand(sema_output, src);
            }
        }
    }

    fn validate_place(&mut self, sema_output: &MirProgram, place: &Place) -> Option<TypeId> {
        match place {
            Place::Local(local_id) => {
                if let Some(local) = sema_output.locals.get(local_id) {
                    Some(local.type_id)
                } else {
                    self.errors.push(ValidationError::LocalNotFound(*local_id));
                    None
                }
            }
            Place::Deref(op) => {
                self.validate_operand(sema_output, op);
                // try to infer pointer pointee type
                if let Some(op_ty) = self.operand_type(sema_output, op) {
                    if let Some(MirType::Pointer { pointee }) = sema_output.types.get(&op_ty) {
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
                if let Some(g) = sema_output.globals.get(gid) {
                    Some(g.type_id)
                } else {
                    self.errors.push(ValidationError::GlobalNotFound(*gid));
                    None
                }
            }
            Place::StructField(base, idx) => {
                if let Some(base_ty) = self.validate_place(sema_output, base) {
                    if let Some(MirType::Record { field_types, .. }) = sema_output.types.get(&base_ty) {
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
                let _ = self.validate_place(sema_output, base);
                // index operand may be complex; index operand validation is handled where used
                None
            }
        }
    }

    fn validate_operand(&mut self, sema_output: &MirProgram, op: &Operand) -> Option<TypeId> {
        match op {
            Operand::Copy(place) => self.validate_place(sema_output, place),
            Operand::Constant(cid) => {
                if sema_output.constants.get(cid).is_none() {
                    self.errors.push(ValidationError::IllegalOperation(format!(
                        "Constant {} not found",
                        cid.get()
                    )));
                }
                None
            }
            Operand::AddressOf(place) => {
                if let Some(base_ty) = self.validate_place(sema_output, place) {
                    // create or lookup a pointer type for base_ty is non-trivial; try to find existing pointer type
                    for (tid, ty) in &sema_output.types {
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
                if !sema_output.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                self.validate_operand(sema_output, inner);
                Some(*type_id)
            }
        }
    }

    fn validate_rvalue(&mut self, sema_output: &MirProgram, r: &Rvalue) -> Option<TypeId> {
        match r {
            Rvalue::Use(op) => self.validate_operand(sema_output, op),
            Rvalue::BinaryIntOp(bin, a, b) => {
                let ta = self.validate_operand(sema_output, a);
                let tb = self.validate_operand(sema_output, b);

                match bin {
                    BinaryIntOp::Eq
                    | BinaryIntOp::Ne
                    | BinaryIntOp::Lt
                    | BinaryIntOp::Le
                    | BinaryIntOp::Gt
                    | BinaryIntOp::Ge => self.find_bool_type(sema_output),
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
                let ta = self.validate_operand(sema_output, a);
                let _tb = self.validate_operand(sema_output, b);

                match bin {
                    BinaryFloatOp::Eq
                    | BinaryFloatOp::Ne
                    | BinaryFloatOp::Lt
                    | BinaryFloatOp::Le
                    | BinaryFloatOp::Gt
                    | BinaryFloatOp::Ge => self.find_bool_type(sema_output),
                    _ => ta,
                }
            }
            Rvalue::UnaryIntOp(u, a) => {
                let ta = self.validate_operand(sema_output, a);
                match u {
                    UnaryIntOp::Neg => ta,
                    UnaryIntOp::BitwiseNot => ta,
                    UnaryIntOp::LogicalNot => self.find_bool_type(sema_output),
                }
            }
            Rvalue::UnaryFloatOp(u, a) => {
                let ta = self.validate_operand(sema_output, a);
                match u {
                    UnaryFloatOp::Neg => ta,
                }
            }
            Rvalue::Cast(type_id, op) => {
                if !sema_output.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                let from_ty = self.validate_operand(sema_output, op);
                if let (Some(from), true) = (from_ty, sema_output.types.contains_key(type_id)) {
                    // basic invalid cast check: disallow casts from record/array/enum/function to non-pointer/scalar types
                    if let Some(MirType::Record { .. } | MirType::Array { .. }) = sema_output.types.get(&from) {
                        if let Some(MirType::Pointer { .. }) = sema_output.types.get(type_id) {
                            // pointer casts allowed
                            // pointer casts allowed
                        } else {
                            let type_obj = sema_output.types.get(type_id).unwrap();
                            if type_obj.is_int() || type_obj.is_float() {
                                self.errors.push(ValidationError::InvalidCast(from, *type_id));
                            }
                        }
                    }
                }
                Some(*type_id)
            }
            Rvalue::PtrAdd(a, b) | Rvalue::PtrSub(a, b) => {
                self.validate_operand(sema_output, a);
                self.validate_operand(sema_output, b);
                None
            }
            Rvalue::PtrDiff(a, b) => {
                self.validate_operand(sema_output, a);
                self.validate_operand(sema_output, b);
                None
            }
            Rvalue::StructLiteral(fields) => {
                for (_idx, op) in fields {
                    self.validate_operand(sema_output, op);
                }
                None
            }
            Rvalue::ArrayLiteral(elems) => {
                for e in elems {
                    self.validate_operand(sema_output, e);
                }
                None
            }
            Rvalue::Load(op) => {
                self.validate_operand(sema_output, op);
                None
            }
            Rvalue::Call(target, args) => {
                self.validate_call_target(sema_output, target);
                for a in args {
                    self.validate_operand(sema_output, a);
                }
                None
            }
            Rvalue::BuiltinVaArg(ap, type_id) => {
                self.validate_operand(sema_output, ap);
                if !sema_output.types.contains_key(type_id) {
                    self.errors.push(ValidationError::TypeNotFound(*type_id));
                }
                Some(*type_id)
            }
        }
    }

    fn validate_call_target(&mut self, sema_output: &MirProgram, target: &CallTarget) {
        match target {
            CallTarget::Direct(fid) => {
                if sema_output.functions.get(fid).is_none() {
                    self.errors.push(ValidationError::FunctionNotFound(*fid));
                }
            }
            CallTarget::Indirect(op) => {
                self.validate_operand(sema_output, op);
            }
        }
    }

    fn operand_type(&mut self, sema_output: &MirProgram, op: &Operand) -> Option<TypeId> {
        self.validate_operand(sema_output, op)
    }
    fn validate_terminator(&mut self, sema_output: &MirProgram, term: &Terminator) {
        match term {
            Terminator::Goto(bid) => {
                if !sema_output.blocks.contains_key(bid) {
                    self.errors.push(ValidationError::BlockNotFound(*bid));
                }
            }
            Terminator::If(cond, then_bb, else_bb) => {
                self.validate_operand(sema_output, cond);
                if !sema_output.blocks.contains_key(then_bb) {
                    self.errors.push(ValidationError::BlockNotFound(*then_bb));
                }
                if !sema_output.blocks.contains_key(else_bb) {
                    self.errors.push(ValidationError::BlockNotFound(*else_bb));
                }
            }
            Terminator::Return(op) => {
                if let Some(op) = op {
                    self.validate_operand(sema_output, op);
                }
            }
            Terminator::Unreachable => {}
        }
    }

    fn find_bool_type(&self, sema_output: &MirProgram) -> Option<TypeId> {
        for (id, ty) in &sema_output.types {
            if matches!(ty, MirType::Bool) {
                return Some(*id);
            }
        }
        None
    }

    fn are_types_compatible(&self, sema_output: &MirProgram, t1: TypeId, t2: TypeId) -> bool {
        if t1 == t2 {
            return true;
        }
        let ty1 = sema_output.types.get(&t1);
        let ty2 = sema_output.types.get(&t2);

        if let (Some(type1), Some(type2)) = (ty1, ty2) {
            match (type1, type2) {
                (MirType::Pointer { pointee: p1 }, MirType::Pointer { pointee: p2 }) => {
                    self.are_types_compatible(sema_output, *p1, *p2)
                }
                (
                    MirType::Array {
                        element: e1, size: s1, ..
                    },
                    MirType::Array {
                        element: e2, size: s2, ..
                    },
                ) => s1 == s2 && self.are_types_compatible(sema_output, *e1, *e2),
                (
                    MirType::Function {
                        return_type: r1,
                        params: pm1,
                    },
                    MirType::Function {
                        return_type: r2,
                        params: pm2,
                    },
                ) => {
                    if pm1.len() != pm2.len() {
                        return false;
                    }
                    self.are_types_compatible(sema_output, *r1, *r2)
                        && pm1
                            .iter()
                            .zip(pm2.iter())
                            .all(|(a, b)| self.are_types_compatible(sema_output, *a, *b))
                }
                _ => type1 == type2,
            }
        } else {
            false
        }
    }
}
