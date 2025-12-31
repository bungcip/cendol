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

pub mod ast_to_mir;
pub mod conversions;
pub mod name_resolver;
pub mod symbol_resolver;
pub mod symbol_table;
pub mod type_registry;
pub mod type_resolver;
pub mod types;
pub mod utils;

#[cfg(test)]
pub mod tests_lowering;
#[cfg(test)]
pub mod tests_mir;

// Re-export key types for public API
pub use ast_to_mir::AstToMirLowerer;
pub use symbol_table::{DefinitionState, Namespace, ScopeId, Symbol, SymbolKind, SymbolRef, SymbolTable};
pub use type_registry::TypeRegistry;
pub use types::{
    ArraySizeType, EnumConstant, FunctionParameter, QualType, StructMember, Type, TypeKind, TypeLayout, TypeQualifiers,
    TypeRef,
};
