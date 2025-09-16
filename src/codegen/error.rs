use thiserror::Error;

use cranelift_codegen::CodegenError as CraneliftCodegenError;

#[derive(Error, Debug)]
pub enum CodegenError {
    #[error("Cranelift error: {0}")]
    Cranelift(#[from] CraneliftCodegenError),
    #[error("Module error: {0}")]
    Module(#[from] cranelift_module::ModuleError),
}
