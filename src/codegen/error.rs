use thiserror::Error;

use cranelift_codegen::CodegenError as CraneliftCodegenError;
use cranelift_module::ModuleError as CraneliftModuleError;

pub type CodegenResult<T> = Result<T, CodegenError>;

/// An error that can occur during code generation.
#[derive(Error, Debug)]
pub enum CodegenError {
    /// An error from the Cranelift code generator.
    #[error("Cranelift error: {0}")]
    Cranelift(#[from] Box<CraneliftCodegenError>),
    /// An error from the Cranelift module.
    #[error("Module error: {0}")]
    Module(#[from] Box<CraneliftModuleError>),
    /// An unknown field was used in a struct initializer.
    #[error("Unknown field `{0}` in initializer")]
    UnknownField(String),
    /// An initializer list was too long.
    #[error("Initializer list too long")]
    InitializerTooLong,
    /// An initializer for a non-struct type was found.
    #[error("Initializer for non-struct type")]
    NotAStruct,
    /// A pointer member access was attempted on a non-pointer type.
    #[error("Pointer member access on non-pointer type")]
    NotAPointer,
    /// An initializer for a non-struct or non-array type was found.
    #[error("Initializer for non-struct or non-array type")]
    NotAStructOrArray,
    /// An array index was not a constant expression.
    #[error("Array index is not a constant expression")]
    NonConstantArrayIndex,
    /// A designator was used for a non-array type.
    #[error("Designator for non-array type")]
    NotAnArray,
    /// An unknown type was encountered.
    #[error("Unknown type: {0}")]
    UnknownType(String),
}
