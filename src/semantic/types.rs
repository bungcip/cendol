//! Type system representation and utilities.
//!
//! This module defines the semantic type system used during analysis,
//! distinct from the syntactic TypeSpecifier constructs used in parsing.

use std::num::NonZeroU16;
use std::{fmt::Display, num::NonZeroU32};

use bitflags::bitflags;
use serde::Serialize;

use crate::ast::{NameId, NodeRef, SourceSpan};

/// Type representation (for semantic analysis)
/// This is a canonical type, distinct from TypeSpecifier which is a syntax construct.
/// Types are stored in a separate Vec<Type> with TypeRef references.
/// invariant:
/// - layout == None for incomplete types
/// - layout is computed according to C abstract machine rules
/// - layout may differ from MIR layout

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub layout: Option<TypeLayout>,
}

#[derive(Debug, Clone)]
pub struct TypeLayout {
    pub size: u16,
    pub alignment: u16,
    pub kind: LayoutKind,
}

#[derive(Debug, Clone)]
pub enum LayoutKind {
    Scalar,
    Array { element: TypeRef, len: u64 },
    Record { fields: Vec<FieldLayout>, is_union: bool },
}

#[derive(Debug, Clone)]
pub struct FieldLayout {
    pub offset: u16,
}

impl Type {
    /// Create a new type with default qualifiers
    /// can only be called by TypeRegistry
    pub(crate) fn new(kind: TypeKind) -> Self {
        Type { kind, layout: None }
    }
}

/// Opaque reference to a canonical type.
/// Internally index + 1 (NonZeroU32 for niche optimization).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct TypeRef(NonZeroU32);

impl TypeRef {
    #[inline]
    pub fn new(n: u32) -> Option<Self> {
        NonZeroU32::new(n).map(TypeRef)
    }

    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }

    #[inline]
    pub fn get(self) -> u32 {
        self.0.get()
    }

    #[inline]
    pub fn raw(self) -> u32 {
        self.0.get()
    }

    #[inline]
    pub unsafe fn from_raw(n: u32) -> Self {
        // SAFETY: The caller must guarantee n corresponds to a valid NonZeroU32.
        unsafe { TypeRef(NonZeroU32::new_unchecked(n)) }
    }
}

impl Display for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeRef({})", self.get())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct QualType(u32);

// bits  0..=27  → TypeRef (28 bit)
// bits 28..=31  → qualifiers (4 bit)

impl QualType {
    const QUAL_BITS: u32 = 4;
    const QUAL_SHIFT: u32 = 28;
    const TY_MASK: u32 = (1 << Self::QUAL_SHIFT) - 1;

    #[inline]
    pub fn new(ty: TypeRef, quals: TypeQualifiers) -> Self {
        debug_assert!(quals.bits() < (1 << Self::QUAL_BITS));
        debug_assert!(ty.raw() < Self::TY_MASK);

        QualType((ty.raw() & Self::TY_MASK) | ((quals.bits() as u32) << Self::QUAL_SHIFT))
    }

    #[inline]
    pub fn unqualified(ty: TypeRef) -> Self {
        Self::new(ty, TypeQualifiers::empty())
    }

    #[inline]
    pub fn ty(self) -> TypeRef {
        // SAFETY: self.0 & TY_MASK is guaranteed to be a valid TypeRef
        // because QualType is constructed with a valid TypeRef which is NonZeroU32
        // and fits in TY_MASK.
        unsafe { TypeRef::from_raw(self.0 & Self::TY_MASK) }
    }

    #[inline]
    pub fn qualifiers(self) -> TypeQualifiers {
        TypeQualifiers::from_bits_truncate((self.0 >> Self::QUAL_SHIFT) as u8)
    }

    #[inline]
    pub fn is_const(self) -> bool {
        self.qualifiers().contains(TypeQualifiers::CONST)
    }
}

impl Display for QualType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Format qualifiers
        let quals = self.qualifiers();
        if !quals.is_empty() {
            write!(f, "{} ", quals)?;
        }

        // Note: For complete type formatting, this would need access to a TypeRegistry
        // to resolve the TypeRef to the actual Type. For now, just show the type ref.
        write!(f, "TypeRef({})", self.ty().get())
    }
}

const _: () = assert!(std::mem::size_of::<QualType>() == 4);

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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArraySizeType {
    Constant(usize),
    Variable(NodeRef), // VLA with size expression type
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

impl Display for TypeQualifiers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.contains(TypeQualifiers::CONST) {
            write!(f, "const")?;
        }
        if self.contains(TypeQualifiers::VOLATILE) {
            write!(f, "volatile")?;
        }
        if self.contains(TypeQualifiers::RESTRICT) {
            write!(f, "restrict")?;
        }
        if self.contains(TypeQualifiers::ATOMIC) {
            write!(f, "_Atomic")?;
        }

        Ok(())
    }
}

impl TypeKind {
    /// Convert this type kind to a basic string representation (C-like syntax)
    /// Note: This doesn't format complex nested types to avoid circular dependencies
    pub fn dump(&self) -> String {
        match self {
            TypeKind::Void => "void".to_string(),
            TypeKind::Bool => "_Bool".to_string(),
            TypeKind::Char { is_signed } => {
                if *is_signed {
                    "char".to_string()
                } else {
                    "unsigned char".to_string()
                }
            }
            TypeKind::Short { is_signed } => {
                if *is_signed {
                    "short".to_string()
                } else {
                    "unsigned short".to_string()
                }
            }
            TypeKind::Int { is_signed } => {
                if *is_signed {
                    "int".to_string()
                } else {
                    "unsigned int".to_string()
                }
            }
            TypeKind::Long {
                is_signed,
                is_long_long,
            } => {
                if *is_long_long {
                    if *is_signed {
                        "long long".to_string()
                    } else {
                        "unsigned long long".to_string()
                    }
                } else if *is_signed {
                    "long".to_string()
                } else {
                    "unsigned long".to_string()
                }
            }
            TypeKind::Float => "float".to_string(),
            TypeKind::Double { is_long_double } => {
                if *is_long_double {
                    "long double".to_string()
                } else {
                    "double".to_string()
                }
            }
            TypeKind::Complex { .. } => "_Complex".to_string(),
            TypeKind::Pointer { .. } => "<pointer>".to_string(),
            TypeKind::Array { .. } => "<array>".to_string(),
            TypeKind::Function { .. } => "<function>".to_string(),
            TypeKind::Record { tag, is_union, .. } => {
                let kind_str = if *is_union { "union" } else { "struct" };
                if let Some(tag_name) = tag {
                    format!("{} {}", kind_str, tag_name)
                } else {
                    format!("{} (anonymous)", kind_str)
                }
            }
            TypeKind::Enum { tag, .. } => {
                if let Some(tag_name) = tag {
                    format!("enum {}", tag_name)
                } else {
                    "enum (anonymous)".to_string()
                }
            }
            TypeKind::Error => "<error>".to_string(),
        }
    }
}

impl Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.dump())
    }
}

/// Function parameter information
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionParameter {
    pub param_type: QualType,
    pub name: Option<NameId>,
}

/// Struct/union member information
#[derive(Debug, Clone, PartialEq)]
pub struct StructMember {
    pub name: Option<NameId>,
    pub member_type: QualType,
    pub bit_field_size: Option<NonZeroU16>,
    pub span: SourceSpan, // for diagnostic
}

/// Enum constant information
#[derive(Debug, Clone, PartialEq)]
pub struct EnumConstant {
    pub name: NameId,
    pub value: i64, // Resolved value
    pub span: SourceSpan,
}
