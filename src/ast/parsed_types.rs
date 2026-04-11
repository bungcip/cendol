//! Parsed type system for the Parser phase.
//!
//! This module defines the syntactic type representations used during parsing,
//! distinct from the semantic type system used during analysis. These types
//! are only relevant in the Parser phase and will be converted to semantic
//! types during the SemanticLowering phase.

use std::num::NonZeroU32;

use serde::Serialize;

use crate::ast::parsed::{ParsedArraySize, TypeSpec};
use crate::ast::{NameId, ParsedNodeRef, ParsedParam, SourceSpan};
use crate::semantic::TypeQualifiers;

/// Type reference for parsed base types
pub type ParsedBaseTypeRef = NonZeroU32;

/// Type reference for parsed declarators
pub type DeclaratorRef = NonZeroU32;

/// A parsed type that represents the syntactic structure of a type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ParsedType {
    pub base: ParsedBaseTypeRef,   // NonZeroU32
    pub declarator: DeclaratorRef, // NonZeroU32
    pub qualifiers: TypeQualifiers,
}

/// Range for struct members in the arena
#[derive(Debug, Clone, Copy)]
pub struct ParsedStructMemberRange {
    pub start: u32,
    pub len: u32,
}

/// Range for function parameters in the arena
#[derive(Debug, Clone, Copy)]
pub struct ParsedParamRange {
    pub start: u32,
    pub len: u32,
}

/// Range for enum values in the arena
#[derive(Debug, Clone, Copy)]
pub struct ParsedEnumRange {
    pub start: u32,
    pub len: u32,
}

// ParsedParam is now in parsed.rs

/// Parsed struct/union member information
#[derive(Debug, Clone)]
pub struct ParsedStructMember {
    pub name: Option<NameId>,
    pub ty: ParsedType,
    pub bit_field_size: Option<u16>,
    pub alignment: Option<u32>,
    pub is_packed: bool,
    pub span: SourceSpan,
}

/// Parsed enum constant information
#[derive(Debug, Clone)]
pub struct ParsedEnumConstant {
    pub name: NameId,
    pub value: Option<i64>, // None for now, resolved later
    pub span: SourceSpan,
}

/// Function flags for declarators
#[derive(Debug, Clone, Copy)]
pub struct FunctionFlags {
    pub is_variadic: bool,
}

/// Parsed base type (the fundamental type specifier)
#[derive(Clone, Debug)]
pub enum ParsedBaseType {
    Builtin(TypeSpec),

    Record {
        tag: Option<NameId>,
        members: Option<ParsedStructMemberRange>, // index range
        is_union: bool,
    },

    Enum {
        tag: Option<NameId>,
        enumerators: Option<ParsedEnumRange>,
        underlying_type: Option<ParsedType>,
    },

    Typedef(NameId),
    Typeof(ParsedType),
    TypeofExpr(ParsedNodeRef),
    TypeofUnqual(ParsedType),
    TypeofUnqualExpr(ParsedNodeRef),
}

#[derive(Debug, Clone)]
pub enum ParsedDeclarator {
    Identifier(Option<NameId>),
    Pointer {
        qualifiers: TypeQualifiers,
        inner: DeclaratorRef,
    },

    Array {
        size: ParsedArraySize,
        inner: DeclaratorRef,
    },

    Function {
        params: ParsedParamRange,
        flags: FunctionFlags,
        inner: DeclaratorRef,
    },

    BitField {
        inner: DeclaratorRef,
        width: ParsedNodeRef,
    },
}

/// Arena for storing parsed type information
/// This provides efficient allocation and referencing for parsed types
#[derive(Clone, Debug, Default)]
pub struct ParsedTypeArena {
    base_types: Vec<ParsedBaseType>,
    declarators: Vec<ParsedDeclarator>,
    params: Vec<ParsedParam>,
    struct_members: Vec<ParsedStructMember>,
    enum_constants: Vec<ParsedEnumConstant>,
}

impl ParsedTypeArena {
    /// Allocate a new base type and return its reference
    pub(crate) fn alloc_base_type(&mut self, base_type: ParsedBaseType) -> ParsedBaseTypeRef {
        let index = self.base_types.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.base_types.push(base_type);
        ParsedBaseTypeRef::new(index).expect("ParsedBaseTypeRef overflow")
    }

    /// Allocate a new declarator and return its reference
    pub(crate) fn alloc_decl(&mut self, declarator: ParsedDeclarator) -> DeclaratorRef {
        let index = self.declarators.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.declarators.push(declarator);
        DeclaratorRef::new(index).expect("DeclaratorRef overflow")
    }

    /// Allocate function parameters and return the range
    pub(crate) fn alloc_params(&mut self, params: Vec<ParsedParam>) -> ParsedParamRange {
        let start = self.params.len() as u32;
        self.params.extend(params);
        let len = self.params.len() as u32 - start;
        ParsedParamRange { start, len }
    }

    /// Allocate struct members and return the range
    pub(crate) fn alloc_struct_members(&mut self, members: Vec<ParsedStructMember>) -> ParsedStructMemberRange {
        let start = self.struct_members.len() as u32;
        self.struct_members.extend(members);
        let len = self.struct_members.len() as u32 - start;
        ParsedStructMemberRange { start, len }
    }

    /// Allocate enum constants and return the range
    pub(crate) fn alloc_enum_constants(&mut self, enumerators: Vec<ParsedEnumConstant>) -> ParsedEnumRange {
        let start = self.enum_constants.len() as u32;
        self.enum_constants.extend(enumerators);
        let len = self.enum_constants.len() as u32 - start;
        ParsedEnumRange { start, len }
    }

    /// Get a base type by reference
    pub(crate) fn get_base_type(&self, base: ParsedBaseTypeRef) -> ParsedBaseType {
        let index = (base.get() - 1) as usize;
        self.base_types[index].clone()
    }

    /// Get a declarator by reference
    pub(crate) fn get_decl(&self, decl: DeclaratorRef) -> ParsedDeclarator {
        let index = (decl.get() - 1) as usize;
        self.declarators[index].clone()
    }

    /// Get function parameters by range
    pub(crate) fn get_params(&self, range: ParsedParamRange) -> &[ParsedParam] {
        let start = range.start as usize;
        let end = start + range.len as usize;
        &self.params[start..end]
    }

    /// Get struct members by range
    pub(crate) fn get_struct_members(&self, range: ParsedStructMemberRange) -> &[ParsedStructMember] {
        let start = range.start as usize;
        let end = start + range.len as usize;
        &self.struct_members[start..end]
    }

    /// Get enum constants by range
    pub(crate) fn get_enum_constants(&self, range: ParsedEnumRange) -> &[ParsedEnumConstant] {
        let start = range.start as usize;
        let end = start + range.len as usize;
        &self.enum_constants[start..end]
    }
}
