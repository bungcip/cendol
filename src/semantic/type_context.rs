//! TypeContext
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use hashbrown::HashMap;
use serde::Serialize;
use std::{fmt::Display, num::NonZeroU32};

use crate::ast::{
    ArraySizeType, EnumConstant, FunctionParameter, NameId, StructMember, Type, TypeKind, TypeLayout, TypeQualifiers,
};

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
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct QualType {
    pub ty: TypeRef,
    pub qualifiers: TypeQualifiers,
}

impl QualType {
    #[inline]
    pub fn new(ty: TypeRef, qualifiers: TypeQualifiers) -> Self {
        Self { ty, qualifiers }
    }

    #[inline]
    pub fn unqualified(ty: TypeRef) -> Self {
        Self {
            ty,
            qualifiers: TypeQualifiers::empty(),
        }
    }
}

impl Display for QualType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Format qualifiers
        if !self.qualifiers.is_empty() {
            write!(f, "{} ", self.qualifiers)?;
        }

        // Note: For complete type formatting, this would need access to a TypeContext
        // to resolve the TypeRef to the actual Type. For now, just show the type ref.
        write!(f, "TypeRef({})", self.ty.get())
    }
}

/// Central arena & factory for semantic types.
///
/// Invariants:
/// - All TypeRef come from this context
/// - Types are never removed
/// - Canonical types are reused when possible
pub struct TypeContext {
    pub types: Vec<Type>,

    // --- Canonicalization caches ---
    pointer_cache: HashMap<TypeRef, TypeRef>,
    #[allow(unused)]
    array_cache: HashMap<(TypeRef, ArraySizeType), TypeRef>,
    function_cache: HashMap<FnSigKey, TypeRef>,

    // --- Common builtin types ---
    pub type_void: TypeRef,
    pub type_bool: TypeRef,
    pub type_short: TypeRef,
    pub type_int: TypeRef,
    pub type_uint: TypeRef,
    pub type_long: TypeRef,
    pub type_long_long: TypeRef,
    pub type_char: TypeRef,
    pub type_short_unsigned: TypeRef,
    pub type_char_unsigned: TypeRef,
    pub type_long_unsigned: TypeRef,
    pub type_long_long_unsigned: TypeRef,
    pub type_float: TypeRef,
    pub type_double: TypeRef,
    pub type_long_double: TypeRef,
    pub type_error: TypeRef,
}

impl TypeContext {
    /// Create a new TypeContext with builtin types initialized.
    pub fn new() -> Self {
        TypeContext {
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),

            // temporary placeholders, overwritten below
            type_void: dummy(),
            type_bool: dummy(),
            type_int: dummy(),
            type_uint: dummy(),
            type_short: dummy(),
            type_long: dummy(),
            type_long_long: dummy(),
            type_char: dummy(),
            type_short_unsigned: dummy(),
            type_char_unsigned: dummy(),
            type_long_unsigned: dummy(),
            type_long_long_unsigned: dummy(),
            type_float: dummy(),
            type_double: dummy(),
            type_long_double: dummy(),
            type_error: dummy(),
        }
    }

    pub fn create_builtin(&mut self) {
        self.type_void = self.alloc(Type::new(TypeKind::Void));
        self.type_bool = self.alloc(Type::new(TypeKind::Bool));
        self.type_int = self.alloc(Type::new(TypeKind::Int { is_signed: true }));
        self.type_uint = self.alloc(Type::new(TypeKind::Int { is_signed: false }));
        self.type_short = self.alloc(Type::new(TypeKind::Short { is_signed: true }));
        self.type_short_unsigned = self.alloc(Type::new(TypeKind::Short { is_signed: false }));
        self.type_long = self.alloc(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: false,
        }));
        self.type_long_unsigned = self.alloc(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: false,
        }));
        self.type_long_long = self.alloc(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: true,
        }));
        self.type_long_long_unsigned = self.alloc(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: true,
        }));
        self.type_char = self.alloc(Type::new(TypeKind::Char { is_signed: true }));
        self.type_char_unsigned = self.alloc(Type::new(TypeKind::Char { is_signed: false }));
        self.type_float = self.alloc(Type::new(TypeKind::Float));
        self.type_double = self.alloc(Type::new(TypeKind::Double { is_long_double: false }));
        self.type_long_double = self.alloc(Type::new(TypeKind::Double { is_long_double: true }));
        self.type_error = self.alloc(Type::new(TypeKind::Error));
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32 + 1;
        let nz = NonZeroU32::new(idx).unwrap();
        self.types.push(ty);
        TypeRef(nz)
    }

    /// Immutable access to a type.
    #[inline]
    #[allow(unused)]
    pub fn get(&self, r: TypeRef) -> &Type {
        &self.types[r.index()]
    }

    /// Mutable access to a type (ONLY for completion).
    #[inline]
    #[allow(unused)]
    pub fn get_mut(&mut self, r: TypeRef) -> &mut Type {
        &mut self.types[r.index()]
    }

    // ============================================================
    // Canonical type constructors
    // ============================================================
    pub fn pointer_to(&mut self, base: TypeRef) -> TypeRef {
        if let Some(&ptr) = self.pointer_cache.get(&base) {
            return ptr;
        }

        let ptr = self.alloc(Type::new(TypeKind::Pointer { pointee: base }));
        self.pointer_cache.insert(base, ptr);
        ptr
    }

    pub fn array_of(&mut self, elem: TypeRef, size: ArraySizeType) -> TypeRef {
        let key = (elem, size.clone());
        if let Some(&arr) = self.array_cache.get(&key) {
            return arr;
        }

        let arr = self.alloc(Type::new(TypeKind::Array {
            element_type: elem,
            size,
        }));
        self.array_cache.insert(key, arr);
        arr
    }

    pub fn function_type(
        &mut self,
        return_type: TypeRef,
        params: Vec<FunctionParameter>,
        is_variadic: bool,
    ) -> TypeRef {
        let key = FnSigKey {
            return_type,
            params: params.iter().map(|p| p.param_type.ty).collect(), // canonical type only
            is_variadic,
        };

        if let Some(&f) = self.function_cache.get(&key) {
            return f;
        }

        let f = self.alloc(Type::new(TypeKind::Function {
            return_type,
            parameters: params,
            is_variadic,
        }));

        self.function_cache.insert(key, f);
        f
    }

    pub fn complex_type(&mut self, base_type: TypeRef) -> TypeRef {
        let complex = self.alloc(Type::new(TypeKind::Complex { base_type }));
        complex
    }

    // ============================================================
    // Record / enum handling (two-phase)
    // ============================================================
    #[allow(unused)]
    pub fn new_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

    pub fn complete_record(&mut self, record: TypeRef, members: Vec<StructMember>, layout: Option<TypeLayout>) {
        let ty = self.get_mut(record);
        match &mut ty.kind {
            TypeKind::Record {
                is_complete,
                members: slot,
                ..
            } => {
                *slot = members;
                *is_complete = true;
                ty.layout = layout;
            }
            _ => unreachable!("complete_record on non-record"),
        }
    }

    #[allow(unused)]
    pub fn new_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> TypeRef {
        // This is a creation function - use create_enum() from other modules
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Vec::new(),
            is_complete: false,
        }))
    }

    /// Create an enum type with forward reference as QualType.
    #[allow(unused)]
    pub fn create_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> QualType {
        let enum_type = self.new_enum(tag, base_type);
        QualType::unqualified(enum_type)
    }

    #[allow(unused)]
    pub fn complete_enum(&mut self, enum_ty: TypeRef, enumerators: Vec<EnumConstant>, layout: Option<TypeLayout>) {
        let ty = self.get_mut(enum_ty);
        match &mut ty.kind {
            TypeKind::Enum {
                is_complete,
                enumerators: slot,
                ..
            } => {
                *slot = enumerators;
                *is_complete = true;
                ty.layout = layout;
            }
            _ => unreachable!("complete_enum on non-enum"),
        }
    }

    #[allow(unused)]
    pub fn decay(&mut self, qt: QualType) -> QualType {
        match &self.get(qt.ty).kind {
            TypeKind::Array { element_type, .. } => {
                let ptr = self.pointer_to(*element_type);
                QualType::new(ptr, qt.qualifiers)
            }
            TypeKind::Function { .. } => {
                let ptr = self.pointer_to(qt.ty); // TypeRef canonical
                QualType::new(ptr, qt.qualifiers)
            }
            _ => qt,
        }
    }

    #[allow(unused)]
    pub fn strip_all(&self, qt: QualType) -> QualType {
        QualType::unqualified(qt.ty)
    }

    #[allow(unused)]
    pub fn merge_qualifiers(&self, base: QualType, add: TypeQualifiers) -> QualType {
        QualType {
            ty: base.ty,
            qualifiers: base.qualifiers | add,
        }
    }
}

// ================================================================
// Helper types
// ================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FnSigKey {
    return_type: TypeRef,
    params: Vec<TypeRef>,
    is_variadic: bool,
}

fn dummy() -> TypeRef {
    // Temporary placeholder before real initialization
    TypeRef(NonZeroU32::new(1).unwrap())
}
