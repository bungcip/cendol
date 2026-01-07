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

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeClass {
    Builtin = 0,
    Pointer = 1,
    Array = 2,
    Function = 3,
    Record = 4,
    Enum = 5,
    Complex = 6,
    // 7 is available
}

impl TypeClass {
    pub fn from_u32(v: u32) -> Self {
        match v {
            0 => Self::Builtin,
            1 => Self::Pointer,
            2 => Self::Array,
            3 => Self::Function,
            4 => Self::Record,
            5 => Self::Enum,
            6 => Self::Complex,
            _ => unreachable!("Invalid TypeClass value: {}", v),
        }
    }
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinType {
    Void = 0,
    Bool = 1,
    Char = 2,
    SChar = 3,
    UChar = 4,
    Short = 5,
    UShort = 6,
    Int = 7,
    UInt = 8,
    Long = 9,
    ULong = 10,
    LongLong = 11,
    ULongLong = 12,
    Float = 13,
    Double = 14,
    LongDouble = 15,
}

impl BuiltinType {
    pub fn from_u32(v: u32) -> Option<Self> {
        match v {
            0 => Some(Self::Void),
            1 => Some(Self::Bool),
            2 => Some(Self::Char),
            3 => Some(Self::SChar),
            4 => Some(Self::UChar),
            5 => Some(Self::Short),
            6 => Some(Self::UShort),
            7 => Some(Self::Int),
            8 => Some(Self::UInt),
            9 => Some(Self::Long),
            10 => Some(Self::ULong),
            11 => Some(Self::LongLong),
            12 => Some(Self::ULongLong),
            13 => Some(Self::Float),
            14 => Some(Self::Double),
            15 => Some(Self::LongDouble),
            _ => None, // Should not happen for 4 bits if all used, but safe fallback
        }
    }
}

/// Opaque reference to a canonical type.
/// Internally index + 1 (NonZeroU32 for niche optimization).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct TypeRef(NonZeroU32);

impl TypeRef {
    // bits  0..=19  → index (1M entries)
    // bits 20..=23  → builtin id (16 builtin)
    // bits 24..=26  → type class (8 kinds)
    // bit  27       → canonical flag

    const INDEX_BITS: u32 = 20;
    const BUILTIN_BITS: u32 = 4;
    const CLASS_BITS: u32 = 3;
    // const CANON_BITS: u32 = 1;

    const BUILTIN_SHIFT: u32 = Self::INDEX_BITS;
    const CLASS_SHIFT: u32 = Self::BUILTIN_SHIFT + Self::BUILTIN_BITS;
    const CANON_SHIFT: u32 = 27;

    const INDEX_MASK: u32 = (1 << Self::INDEX_BITS) - 1;
    const BUILTIN_MASK: u32 = (1 << Self::BUILTIN_BITS) - 1;
    const CLASS_MASK: u32 = (1 << Self::CLASS_BITS) - 1;

    #[inline]
    pub fn new_full(index: u32, class: TypeClass, builtin: Option<BuiltinType>, canonical: bool) -> Option<Self> {
        // We store index + 1 to avoid 0
        let index_stored = index + 1;
        if index_stored > Self::INDEX_MASK {
            return None; // Index too large
        }

        let builtin_val = builtin.map(|b| b as u32).unwrap_or(0);
        let class_val = class as u32;
        let canon_val = if canonical { 1 } else { 0 };

        let mut raw = index_stored;
        raw |= builtin_val << Self::BUILTIN_SHIFT;
        raw |= class_val << Self::CLASS_SHIFT;
        raw |= canon_val << Self::CANON_SHIFT;

        NonZeroU32::new(raw).map(TypeRef)
    }

    // Deprecated/Legacy constructor for transition, assumes minimal info or specific usage
    // DO NOT USE for new code. Only for internal migration if needed.
    // Ideally we remove this, but `TypeRef::new` was used in `dummy()`.
    // We will replace usage in type_registry.
    #[inline]
    pub(crate) unsafe fn from_raw_unchecked(n: u32) -> Self {
        // SAFETY: Caller guarantees n is valid NonZeroU32
        unsafe { TypeRef(NonZeroU32::new_unchecked(n)) }
    }

    #[inline]
    pub fn index(self) -> usize {
        ((self.0.get() & Self::INDEX_MASK) - 1) as usize
    }

    #[inline]
    pub fn class(self) -> TypeClass {
        TypeClass::from_u32((self.0.get() >> Self::CLASS_SHIFT) & Self::CLASS_MASK)
    }

    #[inline]
    pub fn builtin(self) -> Option<BuiltinType> {
        if self.class() != TypeClass::Builtin {
            return None;
        }
        BuiltinType::from_u32((self.0.get() >> Self::BUILTIN_SHIFT) & Self::BUILTIN_MASK)
    }

    #[inline]
    pub fn is_canonical(self) -> bool {
        (self.0.get() >> Self::CANON_SHIFT) & 1 != 0
    }

    #[inline]
    pub fn raw(self) -> u32 {
        self.0.get()
    }

    /// Returns the raw integer value of the TypeRef.
    /// This replaces the old `get()` method which returned the inner NonZeroU32 value.
    /// Used for debugging or unique identification (e.g. MIR lowering).
    #[inline]
    pub fn get(self) -> u32 {
        self.0.get()
    }

    // --- Helpers ---

    #[inline]
    pub fn is_pointer(self) -> bool {
        self.class() == TypeClass::Pointer
    }

    #[inline]
    pub fn is_array(self) -> bool {
        self.class() == TypeClass::Array
    }

    #[inline]
    pub fn is_function(self) -> bool {
        self.class() == TypeClass::Function
    }

    #[inline]
    pub fn is_record(self) -> bool {
        self.class() == TypeClass::Record
    }

    #[inline]
    pub fn is_enum(self) -> bool {
        self.class() == TypeClass::Enum
    }

    #[inline]
    pub fn is_complex(self) -> bool {
        self.class() == TypeClass::Complex
    }

    #[inline]
    pub fn is_builtin(self) -> bool {
        self.class() == TypeClass::Builtin
    }

    #[inline]
    pub fn is_void(self) -> bool {
        matches!(self.builtin(), Some(BuiltinType::Void))
    }

    #[inline]
    pub fn is_integer(self) -> bool {
         match self.builtin() {
             Some(BuiltinType::Bool) | Some(BuiltinType::Char) | Some(BuiltinType::SChar) | Some(BuiltinType::UChar) |
             Some(BuiltinType::Short) | Some(BuiltinType::UShort) | Some(BuiltinType::Int) | Some(BuiltinType::UInt) |
             Some(BuiltinType::Long) | Some(BuiltinType::ULong) | Some(BuiltinType::LongLong) | Some(BuiltinType::ULongLong) => true,
             _ => false,
         }
    }

    #[inline]
    pub fn is_floating(self) -> bool {
        match self.builtin() {
            Some(BuiltinType::Float) | Some(BuiltinType::Double) | Some(BuiltinType::LongDouble) => true,
            _ => false,
        }
    }

    #[inline]
    pub fn is_arithmetic(self) -> bool {
        self.is_integer() || self.is_floating() || self.is_complex()
    }

    #[inline]
    pub fn is_scalar(self) -> bool {
        self.is_arithmetic() || self.is_pointer()
    }
}

impl Display for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeRef(idx={}, class={:?}, builtin={:?})", self.index(), self.class(), self.builtin())
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
        debug_assert!(ty.raw() <= Self::TY_MASK); // <= because mask is 0xFFFFFFF

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
        unsafe { TypeRef::from_raw_unchecked(self.0 & Self::TY_MASK) }
    }

    #[inline]
    pub fn qualifiers(self) -> TypeQualifiers {
        TypeQualifiers::from_bits_truncate((self.0 >> Self::QUAL_SHIFT) as u8)
    }

    #[inline]
    pub fn is_const(self) -> bool {
        self.qualifiers().contains(TypeQualifiers::CONST)
    }

    // Delegate to TypeRef
    #[inline] pub fn is_pointer(self) -> bool { self.ty().is_pointer() }
    #[inline] pub fn is_array(self) -> bool { self.ty().is_array() }
    #[inline] pub fn is_function(self) -> bool { self.ty().is_function() }
    #[inline] pub fn is_record(self) -> bool { self.ty().is_record() }
    #[inline] pub fn is_enum(self) -> bool { self.ty().is_enum() }
    #[inline] pub fn is_complex(self) -> bool { self.ty().is_complex() }
    #[inline] pub fn is_builtin(self) -> bool { self.ty().is_builtin() }
    #[inline] pub fn is_void(self) -> bool { self.ty().is_void() }
    #[inline] pub fn is_integer(self) -> bool { self.ty().is_integer() }
    #[inline] pub fn is_floating(self) -> bool { self.ty().is_floating() }
    #[inline] pub fn is_arithmetic(self) -> bool { self.ty().is_arithmetic() }
    #[inline] pub fn is_scalar(self) -> bool { self.ty().is_scalar() }
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
        write!(f, "{}", self.ty())
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

impl TypeKind {
    pub fn to_class(&self) -> TypeClass {
        match self {
            TypeKind::Void | TypeKind::Bool | TypeKind::Char { .. } |
            TypeKind::Short { .. } | TypeKind::Int { .. } | TypeKind::Long { .. } |
            TypeKind::Float | TypeKind::Double { .. } | TypeKind::Error => TypeClass::Builtin,
            TypeKind::Complex { .. } => TypeClass::Complex,
            TypeKind::Pointer { .. } => TypeClass::Pointer,
            TypeKind::Array { .. } => TypeClass::Array,
            TypeKind::Function { .. } => TypeClass::Function,
            TypeKind::Record { .. } => TypeClass::Record,
            TypeKind::Enum { .. } => TypeClass::Enum,
        }
    }

    pub fn to_builtin(&self) -> Option<BuiltinType> {
         match self {
            TypeKind::Void | TypeKind::Error => Some(BuiltinType::Void),
            TypeKind::Bool => Some(BuiltinType::Bool),
            TypeKind::Char { is_signed: true } => Some(BuiltinType::Char),
            TypeKind::Char { is_signed: false } => Some(BuiltinType::UChar), // Using UChar for unsigned char
            TypeKind::Short { is_signed: true } => Some(BuiltinType::Short),
            TypeKind::Short { is_signed: false } => Some(BuiltinType::UShort),
            TypeKind::Int { is_signed: true } => Some(BuiltinType::Int),
            TypeKind::Int { is_signed: false } => Some(BuiltinType::UInt),
            TypeKind::Long { is_signed: true, is_long_long: false } => Some(BuiltinType::Long),
            TypeKind::Long { is_signed: false, is_long_long: false } => Some(BuiltinType::ULong),
            TypeKind::Long { is_signed: true, is_long_long: true } => Some(BuiltinType::LongLong),
            TypeKind::Long { is_signed: false, is_long_long: true } => Some(BuiltinType::ULongLong),
            TypeKind::Float => Some(BuiltinType::Float),
            TypeKind::Double { is_long_double: false } => Some(BuiltinType::Double),
            TypeKind::Double { is_long_double: true } => Some(BuiltinType::LongDouble),
            _ => None,
        }
    }
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
