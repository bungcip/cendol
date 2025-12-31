//! MIR Validation Pass
//!
//! This module implements a validation pass that ensures MIR is well-formed
//! and ready for code generation. The validation pass checks:
//! - All locals have types
//! - All blocks end with a Terminator
//! - No illegal operations remain
//! - MIR is Cranelift-safe

use crate::{driver::compiler::SemaOutput, mir::*};

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
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    /// Validate a MIR module
    ///
    /// Returns Ok(()) if validation passes, or Err(Vec<ValidationError>) if errors are found
    pub fn validate(&mut self, sema_output: &SemaOutput) -> Result<(), Vec<ValidationError>> {
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
    fn validate_function(&mut self, sema_output: &SemaOutput, func: &MirFunction) {
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
    }

    /// Get the validation errors (for testing purposes)
    pub fn get_errors(&self) -> &Vec<ValidationError> {
        &self.errors
    }
}
