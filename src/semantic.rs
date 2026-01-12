//! Semantic analysis module.
//!
//! This module provides comprehensive semantic analysis for C11 code, including:
//! - Symbol collection and scope management
//! - Name resolution
//! - Type checking
//! - Semantic validation
//! - MIR construction with multi-declarator support
//!
//! The analysis is performed in distinct phases using the visitor pattern
//! for clean separation of concerns and maintainable code.

pub mod analyzer;
pub mod ast_to_mir;
pub mod const_eval;
pub mod conversions;

pub mod lowering;

pub mod symbol_table;
pub mod type_registry;
pub mod types;

#[cfg(test)]
mod tests_enum_const;

// Re-export key types for public API
pub use analyzer::{ImplicitConversion, SemanticInfo, ValueCategory};
pub(crate) use ast_to_mir::AstToMirLowerer;
pub use symbol_table::{DefinitionState, Namespace, ScopeId, SymbolKind, SymbolRef, SymbolTable};
pub use type_registry::TypeRegistry;
pub use types::{
    ArraySizeType, BuiltinType, EnumConstant, FunctionParameter, QualType, StructMember, Type, TypeKind, TypeLayout,
    TypeQualifiers, TypeRef,
};
