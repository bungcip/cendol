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
pub mod name_resolver;
pub mod symbol_resolver;
pub mod symbol_table;
pub mod type_registry;
pub mod types;
pub mod utils;

#[cfg(test)]
mod tests_generic;
#[cfg(test)]
pub mod tests_lowering;
#[cfg(test)]
pub mod tests_mir;
#[cfg(test)]
pub mod tests_validation;

/// Side table containing semantic information for AST nodes.
/// Parallel vectors indexed by node index (NodeRef.get() - 1).
#[derive(Debug, Clone)]
pub struct SemanticInfo {
    pub types: Vec<Option<types::QualType>>,
    pub conversions: Vec<SmallVec<[ImplicitConversion; 1]>>,
    pub value_categories: Vec<ValueCategory>,
}

impl SemanticInfo {
    pub fn with_capacity(n: usize) -> Self {
        use smallvec::SmallVec;
        Self {
            types: vec![None; n],
            conversions: vec![SmallVec::new(); n],
            value_categories: vec![ValueCategory::RValue; n],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueCategory {
    LValue,
    RValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplicitConversion {
    /// LValue → RValue
    LValueToRValue,

    /// Array/function → pointer
    PointerDecay,

    /// char/short → int (store types as TypeRef)
    IntegerPromotion { from: types::TypeRef, to: types::TypeRef },

    /// int → long, unsigned → unsigned long, etc
    IntegerCast { from: types::TypeRef, to: types::TypeRef },

    /// void* ↔ T*
    PointerCast { from: types::TypeRef, to: types::TypeRef },

    /// add/remove const/volatile
    QualifierAdjust {
        from: types::TypeQualifiers,
        to: types::TypeQualifiers,
    },

    /// 0 / NULL → T*
    NullPointerConstant,
}

// Re-export key types for public API
pub use ast_to_mir::AstToMirLowerer;
use smallvec::SmallVec;
pub use symbol_table::{DefinitionState, Namespace, ScopeId, Symbol, SymbolKind, SymbolRef, SymbolTable};
pub use type_registry::TypeRegistry;
pub use types::{
    ArraySizeType, EnumConstant, FunctionParameter, QualType, StructMember, Type, TypeKind, TypeLayout, TypeQualifiers,
    TypeRef,
};
