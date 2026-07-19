//! Parsed type system for the Parser phase.
//!
//! This module defines the syntactic type representations used during parsing,
//! distinct from the semantic type system used during analysis. These types
//! are only relevant in the Parser phase and will be converted to semantic
//! types during the SemanticLowering phase.

use std::num::NonZeroU32;

use serde::Serialize;

use crate::ast::parsed::{DeclSpec, PArraySize, TypeSpec};
use crate::ast::{NameId, PNodeRef, PParam};
use crate::semantic::TypeQuals;

/// Type reference for parsed base types
pub type PBaseTypeRef = NonZeroU32;

/// Type reference for parsed declarators
pub type DeclaratorRef = NonZeroU32;

/// A parsed type that represents the syntactic structure of a type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct PType {
    pub base: PBaseTypeRef,        // NonZeroU32
    pub declarator: DeclaratorRef, // NonZeroU32
    pub quals: TypeQuals,
}

/// Range for function parameters in the arena
#[derive(Debug, Clone, Copy)]
pub struct PParamRange {
    pub start: u32,
    pub len: u32,
}

/// Function flags for declarators
#[derive(Debug, Clone, Copy)]
pub struct FunctionFlags {
    pub is_variadic: bool,
    pub has_prototype: bool,
}

/// Parsed base type (the fundamental type specifier)
#[derive(Clone, Debug)]
pub enum PBaseType {
    Builtin(TypeSpec),
    Typedef(NameId),
    Typeof(PType),
    TypeofExpr(PNodeRef),
    TypeofUnqual(PType),
    TypeofUnqualExpr(PNodeRef),
}

#[derive(Debug, Clone)]
pub enum PDeclarator {
    Identifier(Option<NameId>),
    Pointer {
        quals: TypeQuals,
        inner: DeclaratorRef,
    },

    Array {
        size: PArraySize,
        inner: DeclaratorRef,
    },

    Function {
        params: PParamRange,
        flags: FunctionFlags,
        inner: DeclaratorRef,
        scope_id: crate::semantic::ScopeId,
    },

    BitField {
        inner: DeclaratorRef,
        width: PNodeRef,
    },
    Attribute {
        inner: DeclaratorRef,
        spec: DeclSpec,
    },
}

/// Arena for storing parsed type information
/// This provides efficient allocation and referencing for parsed types
#[derive(Clone, Debug, Default)]
pub struct PTypeArena {
    base_types: Vec<PBaseType>,
    declarators: Vec<PDeclarator>,
    params: Vec<PParam>,
}

impl PTypeArena {
    /// Allocate a new base type and return its reference
    pub(crate) fn alloc_base_type(&mut self, base_type: PBaseType) -> PBaseTypeRef {
        let index = self.base_types.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.base_types.push(base_type);
        PBaseTypeRef::new(index).expect("ParsedBaseTypeRef overflow")
    }

    /// Allocate a new declarator and return its reference
    pub(crate) fn alloc_decl(&mut self, declarator: PDeclarator) -> DeclaratorRef {
        let index = self.declarators.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.declarators.push(declarator);
        DeclaratorRef::new(index).expect("DeclaratorRef overflow")
    }

    /// Allocate function parameters and return the range
    pub(crate) fn alloc_params(&mut self, params: Vec<PParam>) -> PParamRange {
        let start = self.params.len() as u32;
        self.params.extend(params);
        let len = self.params.len() as u32 - start;
        PParamRange { start, len }
    }

    /// Get a base type by reference
    pub(crate) fn get_base_type(&self, base: PBaseTypeRef) -> &PBaseType {
        let index = (base.get() - 1) as usize;
        &self.base_types[index]
    }

    /// Get a declarator by reference
    pub(crate) fn get_decl(&self, decl: DeclaratorRef) -> &PDeclarator {
        let index = (decl.get() - 1) as usize;
        &self.declarators[index]
    }

    /// Get function parameters by range
    pub(crate) fn get_params(&self, range: PParamRange) -> &[PParam] {
        let start = range.start as usize;
        let end = start + range.len as usize;
        &self.params[start..end]
    }

    /// Get the scope ID associated with a function declarator (traversing pointers, arrays, etc.)
    pub(crate) fn get_declarator_scope(&self, decl: DeclaratorRef) -> Option<crate::semantic::ScopeId> {
        match self.get_decl(decl) {
            PDeclarator::Function { scope_id, .. } => Some(*scope_id),
            PDeclarator::Pointer { inner, .. } => self.get_declarator_scope(*inner),
            PDeclarator::Array { inner, .. } => self.get_declarator_scope(*inner),
            PDeclarator::BitField { inner, .. } => self.get_declarator_scope(*inner),
            PDeclarator::Attribute { inner, .. } => self.get_declarator_scope(*inner),
            _ => None,
        }
    }
}
