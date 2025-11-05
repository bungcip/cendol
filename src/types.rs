// Single-thread-friendly TypeTable with TypeId (16-bit index + 16-bit flags).
// Global per-thread table using thread_local! + RefCell to avoid borrow-checker friction.
// - TypeId::new(kind, flags) -> interns into the table and returns TypeId
// - TypeId::get() -> returns a cloned TypeKind so callers don't hold borrows

use paste::paste;
use thin_vec::ThinVec;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::{OnceLock, RwLock};
use bitflags::bitflags;

use crate::StringId;

/// Bitflags for type qualifiers — 1 byte total
bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct TypeQualifiers: u8 {
        const CONST     = 0b0001;
        const VOLATILE  = 0b0010;
        const RESTRICT  = 0b0100;
        const ATOMIC    = 0b1000;
    }
}

/// Primary storage classes — single byte
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum StorageClass {
    None,
    Typedef,
    Extern,
    Static,
    Auto,
    Register,
    ThreadLocal,
}

/// Compact enum for basic type category (8 bytes total with payload)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeSpecKind {
    Builtin(u16),           // bitmask of TypeKeyword flags
    Struct(StringId),       // refers to side-table AggregateDecl
    Union(StringId),
    Enum(StringId),
    Typedef(StringId),
}

/// Simple keyword bitmask — instead of Vec<TypeKeyword>
bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct TypeKeywordMask: u16 {
        const VOID       = 1 << 0;
        const BOOL       = 1 << 1;
        const CHAR       = 1 << 2;
        const SHORT      = 1 << 3;
        const INT        = 1 << 4;
        const LONG       = 1 << 5;
        const LONGLONG   = 1 << 6;
        const FLOAT      = 1 << 7;
        const DOUBLE     = 1 << 8;
        const SIGNED     = 1 << 9;
        const UNSIGNED   = 1 << 10;
        const COMPLEX    = 1 << 11;
        const IMAGINARY  = 1 << 12;
        const ATOMIC     = 1 << 13;
    }
}

/// A lightweight syntactic type specification node
#[derive(Debug, Clone, PartialEq)]
pub struct TypeSpec {
    pub kind: TypeSpecKind,           // 8 bytes
    pub qualifiers: TypeQualifiers,   // 1 byte
    pub storage: StorageClass,        // 1 byte
    pub pointer_depth: u8,            // up to 255 levels
    pub array_rank: u8,               // up to 255 dimensions
    pub alignas: Option<Box<crate::parser::ast::Expr>>,   // optional, rarely used
    pub array_sizes: ThinVec<crate::parser::ast::Expr>,
}

// -----------------------------
// Thread-local global table
// -----------------------------
// Use thread_local + RefCell: cheap and avoids borrow-checker friction for single-threaded compiler.
thread_local! {
    static THREAD_TABLE: RefCell<TypeTable> = RefCell::new(TypeTable::new_with_builtins());
}

include!("generated_types.rs");

// -----------------------------
// TypeId (packed)
// -----------------------------
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TypeId(u32);

impl TypeId {
    const MASK_INDEX: u32 = 0x0000_FFFF;

    /// base kind
    pub const FLAG_POINTER: u16 = 1 << 0;
    pub const FLAG_ARRAY: u16 = 1 << 1;
    pub const FLAG_FUNCTION: u16 = 1 << 2;
    pub const FLAG_RECORD: u16 = 1 << 3; // struct, union
    pub const FLAG_AGGREGATE: u16 = 1 << 4; // struct, union, enum

    /// traits
    pub const FLAG_INTEGER: u16 = 1 << 5;
    pub const FLAG_FLOATING: u16 = 1 << 6;
    pub const FLAG_SIGNED: u16 = 1 << 7;
    pub const FLAG_UNSIGNED: u16 = 1 << 8;

    /// qualifier
    pub const FLAG_CONST: u16 = 1 << 9;
    pub const FLAG_VOLATILE: u16 = 1 << 10;
    pub const FLAG_RESTRICT: u16 = 1 << 11;
    pub const FLAG_ATOMIC: u16 = 1 << 12;

    /// misc
    pub const FLAG_INCOMPLETE: u16 = 1 << 13;
    pub const FLAG_CANONICAL: u16 = 1 << 14;
    pub const FLAG_HAS_NAME: u16 = 1 << 15;

    pub fn with_qualifier(self, q: u16) -> Self {
        let flags = self.flags() | q;
        TypeId::from_parts(self.index(), flags)
    }

    pub fn has_flag(self, flag: u16) -> bool {
        (self.0 & flag as u32) != 0
    }

    pub fn is_const(self) -> bool {
        self.has_flag(Self::FLAG_CONST)
    }
    pub fn is_volatile(self) -> bool {
        self.has_flag(Self::FLAG_VOLATILE)
    }
    pub fn is_restrict(self) -> bool {
        self.has_flag(Self::FLAG_RESTRICT)
    }

    pub fn is_pointer(self) -> bool {
        self.has_flag(Self::FLAG_POINTER)
    }

    pub fn is_record(self) -> bool {
        self.has_flag(Self::FLAG_RECORD)
    }

    pub fn is_aggregate(self) -> bool {
        self.has_flag(Self::FLAG_AGGREGATE)
    }

    pub fn is_floating(self) -> bool {
        self.has_flag(Self::FLAG_FLOATING)
    }

    pub fn is_unsigned(self) -> bool {
        self.has_flag(Self::FLAG_UNSIGNED)
    }

    pub fn get_integer_rank(self) -> i32 {
        self.kind().get_integer_rank()
    }

    // pub fn get_arithmetic_rank(&self) -> i32 {
    //     self.kind().get_arithmetic_rank()
    // }

    pub fn unwrap_const(self) -> Self {
        if self.is_const() {
            self.without_flag(Self::FLAG_CONST)
        } else {
            self
        }
    }

    pub fn unwrap_volatile(self) -> Self {
        if self.is_volatile() {
            self.without_flag(Self::FLAG_VOLATILE)
        } else {
            self
        }
    }

    pub fn without_flag(self, flag: u16) -> Self {
        let flags = self.flags() & !flag;
        TypeId::from_parts(self.index(), flags)
    }

    /// Make from raw index+flags packed.
    pub const fn from_raw(raw: u32) -> Self {
        TypeId(raw)
    }

    /// Make from index (u16) and flags (u16).
    pub const fn from_parts(index: u16, flags: u16) -> Self {
        TypeId(((flags as u32) << 16) | (index as u32))
    }

    /// Create (intern) a TypeKind into the global thread-local TypeTable
    /// and return a TypeId with the provided flags.
    pub fn new(kind: TypeKind, flags: u16) -> Self {
        THREAD_TABLE.with(|tbl| {
            let mut t = tbl.borrow_mut();
            let idx = t.intern_local(&kind);
            TypeId::from_parts(idx, flags)
        })
    }

    /// Return index portion (u16).
    pub const fn index(self) -> u16 {
        (self.0 & Self::MASK_INDEX) as u16
    }

    /// Return flags portion (u16).
    pub const fn flags(self) -> u16 {
        (self.0 >> 16) as u16
    }
}

impl fmt::Debug for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "T#{} (flags=0x{:04X})", self.index(), self.flags())
    }
}

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// interning
impl TypeId {
    /// return cloned TypeKind from TypeId
    pub fn kind(&self) -> TypeKind {
        THREAD_TABLE.with(|tbl| {
            let t = tbl.borrow();
            t.types[self.index() as usize].clone()
        })
    }

    pub fn intern(kind: &TypeKind) -> TypeId {
        Self::intern_with_flags(kind, kind.flags())
    }

    pub fn intern_with_flags(kind: &TypeKind, mut flags: u16) -> TypeId {
        if kind.is_canonical_candidate() {
            flags |= TypeId::FLAG_CANONICAL;
        }

        THREAD_TABLE.with(|tbl| {
            let mut t = tbl.borrow_mut();
            let idx = t.intern_local(kind);
            TypeId::from_parts(idx, flags)
        })
    }

    pub fn pointer_to(base: TypeId) -> TypeId {
        Self::intern(&TypeKind::Pointer(base))
    }

    pub fn const_pointer_to(base: TypeId) -> TypeId {
        Self::intern(&TypeKind::Pointer(base.with_qualifier(TypeId::FLAG_CONST)))
    }
}

/// type shenanigan
impl TypeId {
    /// Canonicalize a type.
    /// If the type is already canonical, returns itself.
    /// Resolves typedefs, pointers, const, and aggregates.
    pub fn canonicalize(self) -> TypeId {
        // cepat kalau sudah canonical
        if self.has_flag(Self::FLAG_CANONICAL) {
            return self;
        }

        THREAD_TABLE.with(|tbl| {
            let mut table = tbl.borrow_mut();
            let kind = table.types[self.index() as usize].clone();

            let canonical_kind = match kind {
                TypeKind::Typedef(_, base) => {
                    base.canonicalize().kind() // resolve ke base
                }
                TypeKind::Pointer(inner) => TypeKind::Pointer(inner.canonicalize()),
                TypeKind::Array(inner, size) => TypeKind::Array(inner.canonicalize(), size),
                TypeKind::Struct(name, fields) => TypeKind::Struct(name, fields),
                TypeKind::Union(name, fields) => {
                    TypeKind::Union(name, fields)
                }
                TypeKind::Enum{name, underlying_type, variants} => TypeKind::Enum{name, underlying_type, variants},
                _ => kind,
            };

            // intern kembali, dengan flag CANONICAL
            let mut flags = canonical_kind.flags();
            flags |= Self::FLAG_CANONICAL;
            let idx = table.intern_local(&canonical_kind);
            TypeId::from_parts(idx, flags)
        })
    }
}

// impl fmt::Display for TypeId {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         // Try to pretty-print builtin names if possible; otherwise fallback to debug.
//         match self.index() {
//             0 => write!(f, "void"),
//             1 => write!(f, "_Bool"),
//             2 => write!(f, "char"),
//             3 => write!(f, "int"),
//             4 => write!(f, "float"),
//             5 => write!(f, "double"),
//             _ => write!(f, "{:?}", self),
//         }
//     }
// }

// TypeKind
// -----------------------------
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Void,
    Bool,
    Char,
    Short,
    Int,
    Long,
    LongLong,
    Float,
    Double,
    UnsignedChar,
    UnsignedShort,
    UnsignedInt,
    UnsignedLong,
    UnsignedLongLong,
    Pointer(TypeId),
    Array(TypeId, usize),

    Struct(Option<StringId>, ThinVec<ParamType>),
    Union(Option<StringId>, ThinVec<ParamType>),
    Enum {
        name: Option<StringId>,
        underlying_type: TypeId,
        variants: ThinVec<EnumVariant>,
    },

    Function {
        return_type: TypeId,
        params: Vec<TypeId>,
        is_variadic: bool,
    },

    Typedef(StringId, TypeId),
    // Error,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct EnumVariant {
    pub name: StringId,      // enumerator name
    pub value: i64,          // integer value assigned
}


#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ParamType {
    pub ty: TypeId,
    pub name: StringId,
}


impl TypeKind {
    /// flag for TypeId
    pub fn flags(&self) -> u16 {
        match self {
// ----- scalar types -----
            TypeKind::Void => 0,
            TypeKind::Bool => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::Char => TypeId::FLAG_INTEGER | TypeId::FLAG_SIGNED,
            TypeKind::UnsignedChar => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::Short => TypeId::FLAG_INTEGER | TypeId::FLAG_SIGNED,
            TypeKind::UnsignedShort => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::Int => TypeId::FLAG_INTEGER | TypeId::FLAG_SIGNED,
            TypeKind::UnsignedInt => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::Long => TypeId::FLAG_INTEGER | TypeId::FLAG_SIGNED,
            TypeKind::UnsignedLong => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::LongLong => TypeId::FLAG_INTEGER | TypeId::FLAG_SIGNED,
            TypeKind::UnsignedLongLong => TypeId::FLAG_INTEGER | TypeId::FLAG_UNSIGNED,
            TypeKind::Float => TypeId::FLAG_FLOATING,
            TypeKind::Double => TypeId::FLAG_FLOATING,

            // ----- pointer types -----
            TypeKind::Pointer(_) => TypeId::FLAG_POINTER,

            // ----- array types -----
            TypeKind::Array(..) => TypeId::FLAG_ARRAY,

            // ----- aggregate / composite types -----
            TypeKind::Struct(Some(_), ..) => TypeId::FLAG_RECORD | TypeId::FLAG_AGGREGATE | TypeId::FLAG_HAS_NAME,
            TypeKind::Struct(None, ..) => TypeId::FLAG_RECORD | TypeId::FLAG_AGGREGATE,
            TypeKind::Union(Some(_), ..) => TypeId::FLAG_RECORD | TypeId::FLAG_AGGREGATE | TypeId::FLAG_HAS_NAME,
            TypeKind::Union(None, ..) => TypeId::FLAG_RECORD | TypeId::FLAG_AGGREGATE,
            TypeKind::Enum{name: Some(_), ..} => TypeId::FLAG_AGGREGATE | TypeId::FLAG_HAS_NAME,
            TypeKind::Enum{name: None, ..} => TypeId::FLAG_AGGREGATE,

            // ----- typedef -----
            TypeKind::Typedef(_, base) => base.flags(),

            // ----- function types -----
            TypeKind::Function{..} => TypeId::FLAG_FUNCTION,
        }
    }

    pub fn is_canonical_candidate(&self) -> bool {
        matches!(
            self,
            TypeKind::Void
                | TypeKind::Bool
                | TypeKind::Char
                | TypeKind::Int
                | TypeKind::Float
                | TypeKind::Double
                | TypeKind::Pointer(_)
        )
    }

    pub fn get_integer_rank(&self) -> i32 {
        match self {
            TypeKind::Bool => 1,
            TypeKind::Char | TypeKind::UnsignedChar => 2,
            TypeKind::Short | TypeKind::UnsignedShort => 3,
            TypeKind::Int | TypeKind::UnsignedInt => 4,
            TypeKind::Long | TypeKind::UnsignedLong => 5,
            TypeKind::LongLong | TypeKind::UnsignedLongLong => 6,
            _ => 0,
        }
    }
}

// -----------------------------
// TypeTable (interning)
// -----------------------------
pub struct TypeTable {
    types: Vec<TypeKind>,
    map: HashMap<TypeKind, u16>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self::new_with_builtins()
    }

    /// Intern `kind` and return its index (u16). If present return existing index.
    fn intern_local(&mut self, kind: &TypeKind) -> u16 {
        if let Some(&idx) = self.map.get(&kind) {
            return idx;
        }
        let idx = self.types.len() as u16;
        self.types.push(kind.clone());
        self.map.insert(kind.clone(), idx);
        idx
    }

}

// -----------------------------
// Examples / tests
// -----------------------------
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_ids_match_interned() {
        assert_eq!(TypeId::intern(&TypeKind::Bool).index(), TypeId::BOOL.index());

        let vptr = TypeId::intern(&TypeKind::Pointer(TypeId::VOID));
        assert_eq!(vptr.index(), TypeId::VOID_PTR.index());

        let cptr = TypeId::intern(&TypeKind::Pointer(TypeId::CHAR));
        assert_eq!(cptr.index(), TypeId::CHAR_PTR.index());

        let iptr = TypeId::intern(&TypeKind::Pointer(TypeId::INT));
        assert_eq!(iptr.index(), TypeId::INT_PTR.index());
    }

}
