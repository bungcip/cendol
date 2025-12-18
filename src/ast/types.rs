//! Type system representation and utilities.
//!
//! This module defines the semantic type system used during analysis,
//! distinct from the syntactic TypeSpecifier constructs used in parsing.

use bitflags::bitflags;
use serde::Serialize;

use crate::ast::{EnumConstant, FunctionParameter, StructMember, Symbol, TypeRef};

/// Type representation (for semantic analysis)
/// This is a canonical type, distinct from TypeSpecifier which is a syntax construct.
/// Types are stored in a separate Vec<Type> with TypeRef references.
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub qualifiers: TypeQualifiers,
    pub size: Option<u16>,      // Computed during semantic analysis
    pub alignment: Option<u16>, // Computed during semantic analysis
}

impl Type {
    /// Create a new type with default qualifiers
    pub fn new(kind: TypeKind) -> Self {
        Type {
            kind,
            qualifiers: TypeQualifiers::empty(),
            size: None,
            alignment: None,
        }
    }

    /// Create a type with specific qualifiers
    pub fn with_qualifiers(kind: TypeKind, qualifiers: TypeQualifiers) -> Self {
        Type {
            kind,
            qualifiers,
            size: None,
            alignment: None,
        }
    }

    /// Check if this is a void type
    pub fn is_void(&self) -> bool {
        matches!(self.kind, TypeKind::Void)
    }

    /// Check if this is an arithmetic type
    pub fn is_arithmetic(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Bool
                | TypeKind::Char { .. }
                | TypeKind::Short { .. }
                | TypeKind::Int { .. }
                | TypeKind::Long { .. }
                | TypeKind::Float
                | TypeKind::Double { .. }
                | TypeKind::Complex { .. }
        )
    }

    /// Check if this is an integer type
    pub fn is_integer(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Bool
                | TypeKind::Char { .. }
                | TypeKind::Short { .. }
                | TypeKind::Int { .. }
                | TypeKind::Long { .. }
        )
    }

    /// Check if this is a floating point type
    pub fn is_floating(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Float | TypeKind::Double { .. } | TypeKind::Complex { .. }
        )
    }

    /// Check if this is a scalar type
    pub fn is_scalar(&self) -> bool {
        self.is_arithmetic() || self.is_pointer() || matches!(self.kind, TypeKind::Enum { .. })
    }

    /// Check if this is a pointer type
    pub fn is_pointer(&self) -> bool {
        matches!(self.kind, TypeKind::Pointer { .. })
    }

    /// Check if this is a complete type
    pub fn is_complete(&self) -> bool {
        match &self.kind {
            TypeKind::Void => false,
            TypeKind::Array { size, .. } => matches!(size, ArraySizeType::Constant(_)),
            TypeKind::Record { is_complete, .. } => *is_complete,
            TypeKind::Enum { is_complete, .. } => *is_complete,
            TypeKind::Incomplete => false,
            _ => true,
        }
    }

    /// Check if this is an array type
    pub fn is_array(&self) -> bool {
        matches!(self.kind, TypeKind::Array { .. })
    }
}

/// The kind of type
#[derive(Debug, Clone)]
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
        tag: Option<Symbol>,
        members: Vec<StructMember>,
        is_complete: bool,
        is_union: bool, // Differentiate between struct and union
    },
    Enum {
        tag: Option<Symbol>,
        base_type: TypeRef, // Underlying integer type
        enumerators: Vec<EnumConstant>,
        is_complete: bool,
    },
    Typedef {
        name: Symbol,
        aliased_type: TypeRef,
    },
    // Placeholder for incomplete types during semantic analysis
    Incomplete,
    Error, // For error recovery
}

/// Array size types
#[derive(Debug, Clone)]
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

impl TypeQualifiers {
    /// Check if qualifiers are compatible (for type compatibility)
    pub fn is_compatible(&self, other: &TypeQualifiers) -> bool {
        // In C, qualifiers can be added but not removed
        // self should be a subset of other or vice versa in some contexts
        // For now, simple equality check
        self == other
    }
}

// FunctionParameter, StructMember, EnumConstant are defined in the main ast module

/// Type utilities and helper functions
pub mod utils {
    use super::*;

    /// Get the size of a type in bytes (if known)
    pub fn type_size(ty: &Type) -> Option<u16> {
        ty.size
    }

    /// Get the alignment of a type in bytes (if known)
    pub fn type_alignment(ty: &Type) -> Option<u16> {
        ty.alignment
    }

    /// Create a pointer type to the given type
    pub fn make_pointer_type(pointee: TypeRef, qualifiers: TypeQualifiers) -> Type {
        Type::with_qualifiers(TypeKind::Pointer { pointee }, qualifiers)
    }

    /// Create an array type
    pub fn make_array_type(element_type: TypeRef, size: ArraySizeType, qualifiers: TypeQualifiers) -> Type {
        Type::with_qualifiers(TypeKind::Array { element_type, size }, qualifiers)
    }

    /// Create a function type
    pub fn make_function_type(return_type: TypeRef, parameters: Vec<FunctionParameter>, is_variadic: bool) -> Type {
        Type::new(TypeKind::Function {
            return_type,
            parameters,
            is_variadic,
        })
    }
}

/// Iterator patterns for AST operations
pub mod iterators {
    use crate::ast::{Ast, NodeRef};

    /// Iterator over child nodes of a node
    pub struct ChildNodeIterator<'a> {
        #[allow(dead_code)]
        ast: &'a Ast,
        children: Vec<NodeRef>,
        index: usize,
    }

    impl<'a> ChildNodeIterator<'a> {
        pub fn new(ast: &'a Ast, node_ref: NodeRef) -> Self {
            let _node = ast.get_node(node_ref);
            let children = Vec::new();
            ChildNodeIterator {
                ast,
                children,
                index: 0,
            }
        }
    }

    impl<'a> Iterator for ChildNodeIterator<'a> {
        type Item = NodeRef;

        fn next(&mut self) -> Option<Self::Item> {
            if self.index < self.children.len() {
                let child = self.children[self.index];
                self.index += 1;
                Some(child)
            } else {
                None
            }
        }
    }

    // Add more iterators as needed...
}
