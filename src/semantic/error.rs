use crate::parser::string_interner::StringId;
use thiserror::Error;

/// An error that can occur during semantic analysis.
#[derive(Error, Debug, Clone)]
pub enum SemanticError {
    /// An undefined function was called.
    #[error("Undefined function `{0}` called")]
    UndefinedFunction(StringId),

    /// An undefined variable was referenced.
    #[error("Undefined variable `{0}`")]
    UndefinedVariable(StringId),

    /// A variable was redeclared in the same scope.
    #[error("Redeclaration of variable `{0}`")]
    VariableRedeclaration(StringId),

    /// A function was redeclared.
    #[error("Redeclaration of function `{0}`")]
    FunctionRedeclaration(StringId),

    /// Type mismatch in expression.
    #[error("Type mismatch in expression")]
    TypeMismatch,

    /// An invalid enum initializer was used.
    #[error("Invalid enum initializer for `{0}`")]
    InvalidEnumInitializer(StringId),

    /// An invalid static initializer was used.
    #[error("Invalid static initializer for `{0}`")]
    InvalidStaticInitializer(String),

    /// Attempted to dereference a non-pointer type.
    #[error("Cannot dereference non-pointer type `{0:?}`")]
    NotAPointer(crate::parser::ast::Type),

    /// An undefined label was referenced in a goto statement.
    #[error("Undefined label `{0}`")]
    UndefinedLabel(StringId),

    /// Assignment to a const-qualified variable.
    #[error("Assignment to const-qualified variable")]
    AssignmentToConst,

    /// Member access on a non-struct/union type.
    #[error("Member access on non-struct/union type `{0:?}`")]
    NotAStructOrUnion(crate::parser::ast::Type),

    /// An undefined member was accessed.
    #[error("Undefined member `{0}`")]
    UndefinedMember(StringId),

    /// Assignment to a non-lvalue expression.
    #[error("Assignment to a non-lvalue expression")]
    NotAnLvalue,

    /// A `_Static_assert` failed.
    #[error("Static assert failed: {0}")]
    StaticAssertFailed(StringId),

    /// A non-constant expression was used where a constant expression was required.
    #[error("Not a constant expression")]
    NotAConstantExpression,

    /// An unused variable was declared.
    #[error("Unused variable `{0}`")]
    UnusedVariable(String),
}

impl SemanticError {
    /// Returns `true` if the error is a warning.
    pub fn is_warning(&self) -> bool {
        matches!(self, SemanticError::UnusedVariable(_))
    }
}
