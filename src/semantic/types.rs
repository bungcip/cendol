//! Type system representation and utilities.
//!
//! This module defines the semantic type system used during analysis,
//! distinct from the syntactic TypeSpecifier constructs used in parsing.

use std::sync::Arc;
use std::{fmt::Display, num::NonZeroU32};

use bitflags::bitflags;
use serde::Serialize;

use crate::ast::{NameId, NodeRef, SourceSpan, StorageClass};

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
    pub size: u64,
    pub alignment: u64,
    pub kind: LayoutKind,
}

#[derive(Debug, Clone)]
pub enum LayoutKind {
    Scalar,
    Array { element: TypeRef, len: u64 },
    Record { fields: Arc<[FieldLayout]>, is_union: bool },
}

#[derive(Debug, Clone)]
pub struct FieldLayout {
    pub offset: u64,
}

impl Type {
    /// Create a new type with default qualifiers
    /// can only be called by TypeRegistry
    pub(crate) fn new(kind: TypeKind) -> Self {
        Type { kind, layout: None }
    }

    pub(crate) fn flatten_members(&self, registry: &super::TypeRegistry, flat_members: &mut Vec<StructMember>) {
        if let TypeKind::Record { members, .. } = &self.kind {
            for member in members.iter().cloned() {
                if member.name.is_none() {
                    let inner_type = registry.get(member.member_type.ty());
                    inner_type.flatten_members(registry, flat_members);
                } else {
                    flat_members.push(member);
                }
            }
        }
    }

    pub(crate) fn flatten_members_with_layouts(
        &self,
        registry: &super::TypeRegistry,
        flat_members: &mut Vec<StructMember>,
        flat_offsets: &mut Vec<u64>,
        base_offset: u64,
    ) {
        if let TypeKind::Record { members, .. } = &self.kind
            && let Some(TypeLayout {
                kind: LayoutKind::Record { fields, .. },
                ..
            }) = &self.layout
        {
            for (i, member) in members.iter().enumerate() {
                let offset = base_offset + fields[i].offset;
                if member.name.is_none() {
                    let inner_type = registry.get(member.member_type.ty());
                    inner_type.flatten_members_with_layouts(registry, flat_members, flat_offsets, offset);
                } else {
                    flat_members.push(*member);
                    flat_offsets.push(offset);
                }
            }
        }
    }

    pub(crate) fn is_union(&self) -> bool {
        matches!(self.kind, TypeKind::Record { is_union: true, .. })
    }

    pub(crate) fn is_record_empty(&self) -> bool {
        if let TypeKind::Record { members, .. } = &self.kind {
            members.is_empty()
        } else {
            false
        }
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
    Typedef = 6,
    Complex = 7,
}

impl TypeClass {
    pub(crate) fn from_u32(v: u32) -> Self {
        match v {
            0 => Self::Builtin,
            1 => Self::Pointer,
            2 => Self::Array,
            3 => Self::Function,
            4 => Self::Record,
            5 => Self::Enum,
            6 => Self::Typedef,
            7 => Self::Complex,
            _ => unreachable!("Invalid TypeClass value: {}", v),
        }
    }
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinType {
    Void = 1,
    Bool = 2,
    Char = 3,
    SChar = 4,
    UChar = 5,
    Short = 6,
    UShort = 7,
    Int = 8,
    UInt = 9,
    Long = 10,
    ULong = 11,
    LongLong = 12,
    ULongLong = 13,
    Float = 14,
    Double = 15,
    LongDouble = 16,
    Signed = 17,
    VaList = 18,
    Complex = 19,
}

impl BuiltinType {
    pub(crate) fn from_u32(v: u32) -> Option<Self> {
        match v {
            1 => Some(Self::Void),
            2 => Some(Self::Bool),
            3 => Some(Self::Char),
            4 => Some(Self::SChar),
            5 => Some(Self::UChar),
            6 => Some(Self::Short),
            7 => Some(Self::UShort),
            8 => Some(Self::Int),
            9 => Some(Self::UInt),
            10 => Some(Self::Long),
            11 => Some(Self::ULong),
            12 => Some(Self::LongLong),
            13 => Some(Self::ULongLong),
            14 => Some(Self::Float),
            15 => Some(Self::Double),
            16 => Some(Self::LongDouble),
            17 => Some(Self::Signed),
            18 => Some(Self::VaList),
            19 => Some(Self::Complex),
            _ => None,
        }
    }

    pub(crate) fn is_integer(self) -> bool {
        matches!(
            self,
            Self::Bool
                | Self::Char
                | Self::SChar
                | Self::UChar
                | Self::Short
                | Self::UShort
                | Self::Int
                | Self::UInt
                | Self::Long
                | Self::ULong
                | Self::LongLong
                | Self::ULongLong
                | Self::Signed // signed int
        )
    }

    pub(crate) fn is_char(self) -> bool {
        matches!(self, Self::Char | Self::SChar | Self::UChar)
    }

    pub(crate) fn is_floating(self) -> bool {
        matches!(self, Self::Float | Self::Double | Self::LongDouble)
    }

    pub(crate) fn is_signed(self) -> bool {
        match self {
            Self::Bool => false,
            Self::Char => true, // Assuming char is signed
            Self::SChar => true,
            Self::UChar => false,
            Self::Short => true,
            Self::UShort => false,
            Self::Int => true,
            Self::UInt => false,
            Self::Long => true,
            Self::ULong => false,
            Self::LongLong => true,
            Self::ULongLong => false,
            Self::Signed => true,
            _ => false,
        }
    }

    pub(crate) fn rank(self) -> u8 {
        match self {
            Self::Bool => 1,
            Self::Char | Self::SChar | Self::UChar => 2,
            Self::Short | Self::UShort => 3,
            Self::Int | Self::UInt | Self::Signed => 4,
            Self::Long | Self::ULong => 5,
            Self::LongLong | Self::ULongLong => 6,
            _ => 0,
        }
    }
}

/// Opaque reference to a canonical type.
/// Internally index + 1 (NonZeroU32 for niche optimization).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct TypeRef(NonZeroU32);

impl TypeRef {
    // Layout:
    // bit  0..=17  (18 bit) → BASE INDEX
    // bit 18..=20  (3 bit)  → TYPE CLASS
    // bit 21..=22  (2 bit)  → POINTER DEPTH (0..3)
    // bit 23..=27  (5 bit)  → ARRAY LEN INLINE (0..31)

    const BASE_BITS: u32 = 18;
    const CLASS_BITS: u32 = 3;
    const PTR_BITS: u32 = 2;
    const ARR_BITS: u32 = 5;

    const BASE_SHIFT: u32 = 0;
    const CLASS_SHIFT: u32 = Self::BASE_BITS;
    const PTR_SHIFT: u32 = Self::CLASS_SHIFT + Self::CLASS_BITS;
    const ARR_SHIFT: u32 = Self::PTR_SHIFT + Self::PTR_BITS;

    const BASE_MASK: u32 = (1 << Self::BASE_BITS) - 1;
    const CLASS_MASK: u32 = (1 << Self::CLASS_BITS) - 1;
    const PTR_MASK: u32 = (1 << Self::PTR_BITS) - 1;
    const ARR_MASK: u32 = (1 << Self::ARR_BITS) - 1;

    #[inline]
    pub(crate) fn new(base_index: u32, class: TypeClass, ptr_depth: u8, arr_len: u32) -> Option<Self> {
        if base_index == 0 || base_index > Self::BASE_MASK {
            return None; // Base index must be non-zero and fit in 18 bits
        }
        if ptr_depth as u32 > Self::PTR_MASK {
            return None;
        }
        if arr_len > Self::ARR_MASK {
            return None;
        }

        // Validate combinations
        match class {
            TypeClass::Builtin => {
                if ptr_depth != 0 || arr_len != 0 {
                    return None;
                }
            }
            TypeClass::Pointer => {
                if arr_len != 0 {
                    return None;
                }
                // Pointer depth 0 means "Registry Pointer" (valid)
                // Pointer depth 1..3 means "Inline Pointer" (valid)
            }
            TypeClass::Array => {
                // Array len 0 means "Registry Array" (valid)
                // Array len 1..31 means "Inline Array" (valid)
                if ptr_depth != 0 {
                    return None;
                }
            }
            TypeClass::Function | TypeClass::Record | TypeClass::Enum | TypeClass::Typedef | TypeClass::Complex => {
                if ptr_depth != 0 || arr_len != 0 {
                    return None;
                }
            }
        }

        let mut raw = 0u32;
        raw |= base_index & Self::BASE_MASK;
        raw |= (class as u32) << Self::CLASS_SHIFT;
        raw |= (ptr_depth as u32) << Self::PTR_SHIFT;
        raw |= (arr_len) << Self::ARR_SHIFT;

        NonZeroU32::new(raw).map(TypeRef)
    }

    // Unsafe constructor for internal use / tests
    #[inline]
    pub(crate) unsafe fn from_raw_unchecked(n: u32) -> Self {
        unsafe { TypeRef(NonZeroU32::new_unchecked(n)) }
    }

    /// Create a dummy TypeRef (value 1) for initialization placeholders.
    /// This is safe because 1 is a valid NonZeroU32, though the TypeRef might not be valid in the registry yet.
    #[inline]
    pub(crate) fn dummy() -> Self {
        unsafe { Self::from_raw_unchecked(1) }
    }

    #[inline]
    pub(crate) fn get(self) -> u32 {
        self.raw()
    }

    #[inline]
    pub(crate) fn base(self) -> u32 {
        (self.0.get() >> Self::BASE_SHIFT) & Self::BASE_MASK
    }

    #[inline]
    pub(crate) fn class(self) -> TypeClass {
        TypeClass::from_u32((self.0.get() >> Self::CLASS_SHIFT) & Self::CLASS_MASK)
    }

    #[inline]
    pub(crate) fn pointer_depth(self) -> u8 {
        ((self.0.get() >> Self::PTR_SHIFT) & Self::PTR_MASK) as u8
    }

    #[inline]
    pub(crate) fn array_len(self) -> Option<u32> {
        let val = (self.0.get() >> Self::ARR_SHIFT) & Self::ARR_MASK;
        if val == 0 { None } else { Some(val) }
    }

    #[inline]
    pub(crate) fn is_builtin(self) -> bool {
        self.class() == TypeClass::Builtin
    }

    #[inline]
    pub(crate) fn is_pointer(self) -> bool {
        self.class() == TypeClass::Pointer
    }

    #[inline]
    pub(crate) fn is_array(self) -> bool {
        self.class() == TypeClass::Array
    }

    #[inline]
    pub(crate) fn is_function(self) -> bool {
        self.class() == TypeClass::Function
    }

    #[inline]
    pub(crate) fn is_record(self) -> bool {
        self.class() == TypeClass::Record
    }

    #[inline]
    pub(crate) fn is_enum(self) -> bool {
        self.class() == TypeClass::Enum
    }

    #[inline]
    pub(crate) fn is_complex(self) -> bool {
        self.class() == TypeClass::Complex
    }

    // --- Helpers for inline/registry check ---

    #[inline]
    pub(crate) fn is_inline_pointer(self) -> bool {
        self.class() == TypeClass::Pointer && self.pointer_depth() != 0
    }

    #[inline]
    pub(crate) fn is_inline_array(self) -> bool {
        self.class() == TypeClass::Array && self.array_len().is_some()
    }
    // --- Legacy/Compat helpers ---

    #[inline]
    pub(crate) fn builtin(self) -> Option<BuiltinType> {
        if self.is_builtin() {
            BuiltinType::from_u32(self.base())
        } else {
            None
        }
    }

    #[inline]
    pub(crate) fn raw(self) -> u32 {
        self.0.get()
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        // Compatibility: returns base as index.
        // For inline types, this returns the index of the base type.
        // For registry types, this returns the registry index.
        self.base() as usize
    }

    #[inline]
    pub(crate) fn is_void(self) -> bool {
        matches!(self.builtin(), Some(BuiltinType::Void))
    }

    #[inline]
    pub(crate) fn is_integer(self) -> bool {
        self.is_enum() || self.builtin().is_some_and(|b| b.is_integer())
    }

    #[inline]
    pub(crate) fn is_floating(self) -> bool {
        self.is_complex() || self.builtin().is_some_and(|b| b.is_floating())
    }

    #[inline]
    pub(crate) fn is_arithmetic(self) -> bool {
        self.is_integer() || self.is_floating()
    }

    #[inline]
    pub(crate) fn is_real(self) -> bool {
        self.is_integer() || self.builtin().is_some_and(|b| b.is_floating())
    }

    #[inline]
    pub(crate) fn is_scalar(self) -> bool {
        self.is_arithmetic() || self.is_pointer()
    }
}

impl Display for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_builtin() {
            write!(f, "{:?}", self.builtin().unwrap())
        } else {
            write!(
                f,
                "TypeRef(base={}, class={:?}, ptr={}, arr={:?})",
                self.base(),
                self.class(),
                self.pointer_depth(),
                self.array_len()
            )
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct QualType(u32);

impl Default for QualType {
    fn default() -> Self {
        // Use raw value 1 (which maps to TypeRef(1)) as default to avoid NonZeroU32(0) UB
        QualType(1)
    }
}

// bits  0..=27  → TypeRef (28 bit)
// bits 28..=31  → qualifiers (4 bit)

impl QualType {
    const QUAL_BITS: u32 = 4;
    const QUAL_SHIFT: u32 = 28;
    const TY_MASK: u32 = (1 << Self::QUAL_SHIFT) - 1;

    #[inline]
    pub(crate) fn new(ty: TypeRef, quals: TypeQualifiers) -> Self {
        debug_assert!(quals.bits() < (1 << Self::QUAL_BITS));
        debug_assert!(ty.raw() <= Self::TY_MASK);

        QualType((ty.raw() & Self::TY_MASK) | ((quals.bits() as u32) << Self::QUAL_SHIFT))
    }

    #[inline]
    pub(crate) fn unqualified(ty: TypeRef) -> Self {
        Self::new(ty, TypeQualifiers::empty())
    }

    #[inline]
    pub(crate) fn ty(self) -> TypeRef {
        unsafe { TypeRef::from_raw_unchecked(self.0 & Self::TY_MASK) }
    }

    #[inline]
    pub(crate) fn qualifiers(self) -> TypeQualifiers {
        TypeQualifiers::from_bits_truncate((self.0 >> Self::QUAL_SHIFT) as u8)
    }

    #[inline]
    pub(crate) fn is_const(self) -> bool {
        self.qualifiers().contains(TypeQualifiers::CONST)
    }

    #[inline]
    pub(crate) fn is_pointer(self) -> bool {
        self.ty().is_pointer()
    }
    #[inline]
    pub(crate) fn is_array(self) -> bool {
        self.ty().is_array()
    }
    #[inline]
    pub(crate) fn is_function(self) -> bool {
        self.ty().is_function()
    }
    #[inline]
    pub(crate) fn is_record(self) -> bool {
        self.ty().is_record()
    }
    #[inline]
    pub(crate) fn is_complex(self) -> bool {
        self.ty().is_complex()
    }
    #[inline]
    pub(crate) fn is_void(self) -> bool {
        self.ty().is_void()
    }
    #[inline]
    pub(crate) fn is_integer(self) -> bool {
        self.ty().is_integer()
    }
    #[inline]
    pub(crate) fn is_arithmetic(self) -> bool {
        self.ty().is_arithmetic()
    }
    #[inline]
    pub(crate) fn is_real(self) -> bool {
        self.ty().is_real()
    }
    #[inline]
    pub(crate) fn is_scalar(self) -> bool {
        self.ty().is_scalar()
    }
}

impl Display for QualType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let quals = self.qualifiers();
        if !quals.is_empty() {
            write!(f, "{} ", quals)?;
        }
        write!(f, "{}", self.ty())
    }
}

const _: () = assert!(std::mem::size_of::<QualType>() == 4);

/// The kind of type
#[derive(Debug, Clone, PartialEq, Default)]
pub enum TypeKind {
    Builtin(BuiltinType),
    Complex {
        base_type: TypeRef,
    },
    Pointer {
        pointee: QualType,
    },
    Array {
        element_type: TypeRef,
        size: ArraySizeType,
    },
    Function {
        return_type: TypeRef,
        parameters: Arc<[FunctionParameter]>,
        is_variadic: bool,
        is_noreturn: bool,
    },
    Record {
        tag: Option<NameId>,
        members: Arc<[StructMember]>,
        is_complete: bool,
        is_union: bool,
    },
    Enum {
        tag: Option<NameId>,
        base_type: TypeRef,
        enumerators: Arc<[EnumConstant]>,
        is_complete: bool,
    },
    #[default]
    Error,
}

impl TypeKind {
    pub(crate) fn builtin(&self) -> Option<BuiltinType> {
        match self {
            TypeKind::Builtin(b) => Some(*b),
            _ => None,
        }
    }

    pub(crate) fn to_class(&self) -> TypeClass {
        match self {
            TypeKind::Builtin(_) | TypeKind::Error => TypeClass::Builtin,
            TypeKind::Complex { .. } => TypeClass::Complex,
            TypeKind::Pointer { .. } => TypeClass::Pointer,
            TypeKind::Array { .. } => TypeClass::Array,
            TypeKind::Function { .. } => TypeClass::Function,
            TypeKind::Record { .. } => TypeClass::Record,
            TypeKind::Enum { .. } => TypeClass::Enum,
        }
    }
}

impl Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Builtin(b) => match b {
                BuiltinType::Void => write!(f, "void"),
                BuiltinType::Bool => write!(f, "_Bool"),
                BuiltinType::Char => write!(f, "char"),
                BuiltinType::SChar => write!(f, "signed char"),
                BuiltinType::UChar => write!(f, "unsigned char"),
                BuiltinType::Short => write!(f, "short"),
                BuiltinType::UShort => write!(f, "unsigned short"),
                BuiltinType::Int => write!(f, "int"),
                BuiltinType::UInt => write!(f, "unsigned int"),
                BuiltinType::Long => write!(f, "long"),
                BuiltinType::ULong => write!(f, "unsigned long"),
                BuiltinType::LongLong => write!(f, "long long"),
                BuiltinType::ULongLong => write!(f, "unsigned long long"),
                BuiltinType::Float => write!(f, "float"),
                BuiltinType::Double => write!(f, "double"),
                BuiltinType::LongDouble => write!(f, "long double"),
                BuiltinType::Signed => write!(f, "signed"),
                BuiltinType::VaList => write!(f, "__builtin_va_list"),
                BuiltinType::Complex => write!(f, "_Complex (marker)"),
            },
            TypeKind::Complex { .. } => write!(f, "_Complex"),
            TypeKind::Pointer { .. } => write!(f, "<pointer>"),
            TypeKind::Array { .. } => write!(f, "<array>"),
            TypeKind::Function { .. } => write!(f, "<function>"),
            TypeKind::Record { tag, is_union, .. } => {
                let kind_str = if *is_union { "union" } else { "struct" };
                if let Some(tag_name) = tag {
                    write!(f, "{} {}", kind_str, tag_name)
                } else {
                    write!(f, "{} (anonymous)", kind_str)
                }
            }
            TypeKind::Enum { tag, .. } => {
                if let Some(tag_name) = tag {
                    write!(f, "enum {}", tag_name)
                } else {
                    write!(f, "enum (anonymous)")
                }
            }
            TypeKind::Error => write!(f, "<error>"),
        }
    }
}

/// Array size types
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArraySizeType {
    Constant(usize),
    Variable(NodeRef),
    Incomplete,
    Star,
}

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Default)]
    pub struct TypeQualifiers: u8 {
        const CONST = 1 << 0;
        const VOLATILE = 1 << 1;
        const RESTRICT = 1 << 2;
        const ATOMIC = 1 << 3;
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FunctionParameter {
    pub param_type: QualType,
    pub name: Option<NameId>,
    pub storage: Option<StorageClass>,
}

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct StructMember {
    pub name: Option<NameId>,
    pub member_type: QualType,
    pub bit_field_size: Option<u16>,
    pub alignment: Option<u32>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct EnumConstant {
    pub name: NameId,
    pub value: i64,
    pub span: SourceSpan,
    pub init_expr: Option<NodeRef>,
}
