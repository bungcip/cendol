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
pub mod const_eval;
pub mod conversions;
pub mod errors;
pub(crate) mod literal_utils;
pub mod lowering;
pub mod symbol_table;
pub mod type_registry;
pub mod types;

pub use analyzer::{Conversion, SemanticInfo, ValueCategory};
pub use symbol_table::{
    BuiltinFunctionKind, DefinitionState, Namespace, ScopeId, SymbolClass, SymbolKind, SymbolRef, SymbolTable, Variable,
};

pub use type_registry::TypeRegistry;
pub use types::{
    ArraySize, BuiltinType, EnumConstant, FieldLayout, FunctionParam, QualType, RecordMember, Type, TypeKind,
    TypeLayout, TypeQualifiers, TypeRef,
};
