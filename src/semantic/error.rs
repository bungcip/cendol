use thiserror::Error;

/// An error that can occur during semantic analysis.
#[derive(Error, Debug)]
pub enum SemanticError {
    /// An undefined function was called.
    #[error("Undefined function `{0}` called")]
    UndefinedFunction(String),

    /// An undefined variable was referenced.
    #[error("Undefined variable `{0}`")]
    UndefinedVariable(String),

    /// A variable was redeclared in the same scope.
    #[error("Redeclaration of variable `{0}`")]
    VariableRedeclaration(String),

    /// A function was redeclared.
    #[error("Redeclaration of function `{0}`")]
    FunctionRedeclaration(String),

    /// Type mismatch in expression.
    #[error("Type mismatch in expression")]
    TypeMismatch,

    /// An invalid enum initializer was used.
    #[error("Invalid enum initializer for `{0}`")]
    InvalidEnumInitializer(String),
}
