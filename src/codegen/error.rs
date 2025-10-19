use thiserror::Error;

use cranelift_codegen::CodegenError as CraneliftCodegenError;

/// An error that can occur during code generation.
#[derive(Error, Debug)]
pub enum CodegenError {
    /// An error from the Cranelift code generator.
    #[error("Cranelift error: {0}")]
    Cranelift(#[from] CraneliftCodegenError),
    /// An error from the Cranelift module.
    #[error("Module error: {0}")]
    Module(#[from] cranelift_module::ModuleError),
}
