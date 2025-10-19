use thiserror::Error;

use cranelift_codegen::CodegenError as CraneliftCodegenError;
use cranelift_module::ModuleError as CraneliftModuleError;

/// An error that can occur during code generation.
#[derive(Error, Debug)]
pub enum CodegenError {
    /// An error from the Cranelift code generator.
    #[error("Cranelift error: {0}")]
    Cranelift(#[from] Box<CraneliftCodegenError>),
    /// An error from the Cranelift module.
    #[error("Module error: {0}")]
    Module(#[from] Box<CraneliftModuleError>),
}
