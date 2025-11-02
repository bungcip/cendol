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

    /// A non-integer expression was used as the condition of a switch statement.
    #[error("Switch condition is not an integer")]
    SwitchConditionNotInteger,

    /// A case label was used outside of a switch statement.
    #[error("Case label outside of switch statement")]
    CaseOutsideSwitch,

    /// A default label was used outside of a switch statement.
    #[error("Default label outside of switch statement")]
    DefaultOutsideSwitch,

    /// A duplicate case label was used in a switch statement.
    #[error("Duplicate case label in switch statement with value `{0}`")]
    DuplicateCaseLabel(i64),

    /// A duplicate default label was used in a switch statement.
    #[error("Duplicate default label in switch statement")]
    DuplicateDefaultLabel,

    /// A break statement was used outside of a loop or switch statement.
    #[error("Break statement outside of loop or switch statement")]
    BreakOutsideLoopOrSwitch,

    /// A continue statement was used outside of a loop.
    #[error("Continue statement outside of loop")]
    ContinueOutsideLoop,

    /// An array index was out of bounds.
    #[error("Array index out of bounds")]
    ArrayIndexOutOfBounds,
}

impl SemanticError {
    /// Returns `true` if the error is a warning.
    pub fn is_warning(&self) -> bool {
        matches!(self, SemanticError::UnusedVariable(_))
    }
}
