//! Type system representation and utilities.
//!
//! This module defines the semantic type system used during analysis,
//! distinct from the syntactic TypeSpecifier constructs used in parsing.

use bitflags::bitflags;
use serde::Serialize;

use crate::ast::{EnumConstant, NameId, StructMember, TypeRef};

/// Type representation (for semantic analysis)
/// This is a canonical type, distinct from TypeSpecifier which is a syntax construct.
/// Types are stored in a separate Vec<Type> with TypeRef references.
#[derive(Debug, Clone, Default)]
pub struct Type {
    pub kind: TypeKind,
    pub qualifiers: TypeQualifiers,
    pub layout: Option<TypeLayout>,
}

#[derive(Debug, Clone, Default)]
pub struct TypeLayout {
    #[allow(unused)]
    size: u16,
    #[allow(unused)]
    alignment: u16,
}

impl Type {
    /// Create a new type with default qualifiers
    pub(crate) fn new(kind: TypeKind) -> Self {
        Type {
            kind,
            qualifiers: TypeQualifiers::empty(),
            layout: None,
        }
    }
}

/// The kind of type
#[derive(Debug, Clone, PartialEq, Default)]
pub enum TypeKind {
    Void,
    Bool,
    Char {
        is_signed: bool,
    },
    Short {
        is_signed: bool,
    },
    Int {
        is_signed: bool,
    },
    Long {
        is_signed: bool,
        is_long_long: bool,
    },
    Float,
    Double {
        is_long_double: bool,
    },
    Complex {
        base_type: TypeRef,
    }, // C11 _Complex
    Atomic {
        base_type: TypeRef,
    }, // C11 _Atomic
    Pointer {
        pointee: TypeRef,
    },
    Array {
        element_type: TypeRef,
        size: ArraySizeType,
    },
    Function {
        return_type: TypeRef,
        parameters: Vec<FunctionParameter>,
        is_variadic: bool,
    },
    Record {
        // Represents both struct and union
        tag: Option<NameId>,
        members: Vec<StructMember>,
        is_complete: bool,
        is_union: bool, // Differentiate between struct and union
    },
    Enum {
        tag: Option<NameId>,
        base_type: TypeRef, // Underlying integer type
        enumerators: Vec<EnumConstant>,
        is_complete: bool,
    },
    #[default]
    Error, // For error recovery
}

/// Array size types
#[derive(Debug, Clone, PartialEq)]
pub enum ArraySizeType {
    Constant(usize),
    Variable(TypeRef), // VLA with size expression type
    Incomplete,
    Star, // [*] for function parameters
}

bitflags! {
    /// Type qualifiers (using bitflags for efficient storage)
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Default)]
    pub struct TypeQualifiers: u8 {
        const CONST = 1 << 0;
        const VOLATILE = 1 << 1;
        const RESTRICT = 1 << 2;
        const ATOMIC = 1 << 3; // C11 _Atomic
    }
}

impl TypeQualifiers {}

/// Function parameter information
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionParameter {
    pub param_type: TypeRef,
    pub name: Option<NameId>,
}

// StructMember, EnumConstant are defined in the main ast module
